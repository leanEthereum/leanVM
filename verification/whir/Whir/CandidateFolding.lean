import Whir.AdditiveColumn
import Whir.JohnsonMCA
import Whir.ReplayRefinement
import Whir.FieldCardinality

/-! Commitment-fixed coefficient lists and same-set MCA lifting through the
executable array folds. Both physical lane orders are represented explicitly. -/
namespace Whir.CandidateFolding
open Concrete MutualAgreement
open scoped BigOperators

variable {F I : Type*} [Field F]

/-- One coefficient table per lane, with a single common agreement set. -/
def Agrees {k lanes : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (oracle : Fin lanes → I → F) (threshold : ℕ)
    (table : Fin lanes → Fin k → F) : Prop :=
  ∃ T : Finset I, threshold ≤ T.card ∧ ∀ lane i, i ∈ T →
    enc (table lane) i = oracle lane i

noncomputable def candidates [Fintype F] {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin lanes → I → F)
    (threshold : ℕ) : Finset (Fin lanes → Fin k → F) := by
  classical
  exact Finset.univ.filter (Agrees enc oracle threshold)

@[simp] theorem mem_candidates [Fintype F] {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin lanes → I → F)
    (threshold : ℕ) (table : Fin lanes → Fin k → F) :
    table ∈ candidates enc oracle threshold ↔ Agrees enc oracle threshold table := by
  classical
  simp [candidates]

/-- Bounded adjacent-lane indices, independent of physical array order. -/
def evenLane {lanes : ℕ} (lane : Fin lanes) : Fin (lanes * 2) :=
  ⟨2 * lane.val, by omega⟩
def oddLane {lanes : ℕ} (lane : Fin lanes) : Fin (lanes * 2) :=
  ⟨2 * lane.val + 1, by omega⟩

def foldTable {k lanes : ℕ} (table : Fin (lanes * 2) → Fin k → F) (z : F) :
    Fin lanes → Fin k → F :=
  fun lane j => (1-z) * table (evenLane lane) j + z * table (oddLane lane) j

def foldOracle {lanes : ℕ} (oracle : Fin (lanes * 2) → I → F) (z : F) :
    Fin lanes → I → F :=
  fun lane i => (1-z) * oracle (evenLane lane) i + z * oracle (oddLane lane) i

/-- Actual codeword folding commutes with every linear row encoder. -/
theorem encode_foldTable {k lanes : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (table : Fin (lanes * 2) → Fin k → F) (z : F) (lane : Fin lanes) :
    enc (foldTable table z lane) =
      (1-z) • enc (table (evenLane lane)) + z • enc (table (oddLane lane)) := by
  change enc ((1-z) • table (evenLane lane) + z • table (oddLane lane)) = _
  simp only [map_add, map_smul]

/-- Interleave two tables using quotient/remainder, including the empty case. -/
def joinTable {k lanes : ℕ} (p₀ p₁ : Fin lanes → Fin k → F) :
    Fin (lanes * 2) → Fin k → F := fun lane =>
  if lane.val % 2 = 0 then p₀ ⟨lane.val / 2, by omega⟩
  else p₁ ⟨lane.val / 2, by omega⟩

omit [Field F] in
@[simp] theorem joinTable_even {k lanes : ℕ} (p₀ p₁ : Fin lanes → Fin k → F)
    (lane : Fin lanes) : joinTable p₀ p₁ (evenLane lane) = p₀ lane := by
  simp [joinTable, evenLane]
omit [Field F] in
@[simp] theorem joinTable_odd {k lanes : ℕ} (p₀ p₁ : Fin lanes → Fin k → F)
    (lane : Fin lanes) : joinTable p₀ p₁ (oddLane lane) = p₁ lane := by
  simp [joinTable, oddLane, Nat.add_div]

/-- Decode the MCA witnesses and correct inside the encoder kernel. Thus no
injectivity or extra domain-size premise is needed to lift the *given* table. -/
theorem coefficient_lifts [Fintype F] {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (C : Submodule F (I → F))
    (range_eq : LinearMap.range enc = C)
    (oracle : Fin (lanes * 2) → I → F) (threshold : ℕ) (z : F)
    (good : ¬ RowBad foldGenerator C threshold
      ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)] z)
    (v : Fin lanes → Fin k → F)
    (hv : v ∈ candidates enc (foldOracle oracle z) threshold) :
    ∃ p ∈ candidates enc oracle threshold, v = foldTable p z := by
  classical
  obtain ⟨T, hT, hagree⟩ := (mem_candidates _ _ _ _).mp hv
  have hmem (lane : Fin lanes) : enc (v lane) ∈ C := by
    rw [← range_eq]
    exact LinearMap.mem_range_self enc _
  obtain ⟨P₀, P₁, hP, hPT, hfold⟩ := fold_candidate_lifts C threshold
    (fun lane => oracle (evenLane lane)) (fun lane => oracle (oddLane lane))
    (fun lane => enc (v lane)) z hmem T hT hagree good
  have hdecode (lane : Fin lanes) :
      ∃ a b : Fin k → F, enc a = P₀ lane ∧ enc b = P₁ lane := by
    have h₀ := (hP lane).1
    have h₁ := (hP lane).2
    rw [← range_eq] at h₀ h₁
    obtain ⟨a, ha⟩ := h₀
    obtain ⟨b, hb⟩ := h₁
    exact ⟨a, b, ha, hb⟩
  choose a b ha hb using hdecode
  let d := fun lane => b lane - a lane
  let p₀ := fun lane => v lane - z • d lane
  let p₁ := fun lane => p₀ lane + d lane
  have hp₀ (lane : Fin lanes) : enc (p₀ lane) = P₀ lane := by
    funext i
    simp only [p₀, d, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, ha, hb, hfold]
    ring
  have hp₁ (lane : Fin lanes) : enc (p₁ lane) = P₁ lane := by
    simp only [p₁, d, map_add, map_sub, hp₀, ha, hb]
    abel
  refine ⟨joinTable p₀ p₁, (mem_candidates _ _ _ _).mpr ⟨T, hT, ?_⟩, ?_⟩
  · intro lane i hi
    let l : Fin lanes := ⟨lane.val / 2, by omega⟩
    by_cases he : lane.val % 2 = 0
    · have hl : evenLane l = lane := by apply Fin.ext; simp only [evenLane, l]; omega
      rw [← hl, joinTable_even, hp₀]
      exact (hPT l i hi).1
    · have hl : oddLane l = lane := by apply Fin.ext; simp only [oddLane, l]; omega
      rw [← hl, joinTable_odd, hp₁]
      exact (hPT l i hi).2
  · funext lane j
    simp only [foldTable, joinTable_even, joinTable_odd, p₀, p₁, d,
      Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

/-- Novel-basis row encoder, the polynomial proved by AdditiveColumn to be
computed by the executable dense column kernel. -/
noncomputable def novelEncoder (basis : ℕ → F) (n : ℕ) (domain : I → F) :
    (Fin (2^n) → F) →ₗ[F] (I → F) where
  toFun a i := (AdditiveCode.polynomial basis n a).eval (domain i)
  map_add' a b := by
    funext i
    simp [AdditiveCode.polynomial, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp only [AdditiveCode.polynomial, Pi.smul_apply, smul_eq_mul,
      mul_smul, ← Finset.smul_sum, Polynomial.eval_smul, RingHom.id_apply]

/-- RS identification is derived from the novel-basis spanning theorem. -/
theorem novelEncoder_range [CharP F 2] (basis : ℕ → F) (n : ℕ)
    (independent : AdditiveCode.Independent basis n) (domain : I → F) :
    LinearMap.range (novelEncoder basis n domain) = rsCode domain (2^n) := by
  ext word
  rw [mem_rsCode]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, AdditiveCode.polynomial_degree_lt independent a, fun _ => rfl⟩
  · rintro ⟨p, hp, he⟩
    obtain ⟨a, ha⟩ := (AdditiveCode.polynomial_surjective independent p).mpr hp
    exact ⟨a, by funext i; simpa [novelEncoder, ha] using he i⟩

/-- Column-major and row-major bounded index equivalences. -/
def topIndex (lanes k : ℕ) : Fin lanes × Fin k ≃ Fin (lanes * k) :=
  finProdFinEquiv
def lowIndex (lanes k : ℕ) : Fin lanes × Fin k ≃ Fin (lanes * k) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm k lanes)))

def packTop {k lanes : ℕ} (table : Fin lanes → Fin k → F) : Array F :=
  Array.ofFn fun i => table ((topIndex lanes k).symm i).1 ((topIndex lanes k).symm i).2
def packLow {k lanes : ℕ} (table : Fin lanes → Fin k → F) : Array F :=
  Array.ofFn fun i => table ((lowIndex lanes k).symm i).1 ((lowIndex lanes k).symm i).2

omit [Field F] in
@[simp] theorem size_packTop {k lanes : ℕ} (table : Fin lanes → Fin k → F) :
    (packTop table).size = lanes * k := by simp [packTop]
omit [Field F] in
@[simp] theorem size_packLow {k lanes : ℕ} (table : Fin lanes → Fin k → F) :
    (packLow table).size = lanes * k := by simp [packLow]

omit [Field F] in
theorem get_packTop [Inhabited F] {k lanes : ℕ}
    (table : Fin lanes → Fin k → F) (lane : Fin lanes) (j : Fin k) :
    (packTop table)[lane.val * k + j.val]! = table lane j := by
  have h : lane.val * k + j.val = (topIndex lanes k (lane,j)).val := by
    simp [topIndex, Nat.add_comm, Nat.mul_comm]
  rw [h]
  simp [packTop]

omit [Field F] in
theorem get_packLow [Inhabited F] {k lanes : ℕ}
    (table : Fin lanes → Fin k → F) (lane : Fin lanes) (j : Fin k) :
    (packLow table)[j.val * lanes + lane.val]! = table lane j := by
  have h : j.val * lanes + lane.val = (lowIndex lanes k (lane,j)).val := by
    simp [lowIndex, Nat.add_comm, Nat.mul_comm]
  rw [h]
  simp [packLow]

private theorem foldPair_eq [CharP F 2] (a b z : F) :
    foldPair a b z = (1-z)*a + z*b := by
  simp only [foldPair]
  linear_combination z * CharTwo.add_self_eq_zero a

theorem packTop_fold [Inhabited F] [CharP F 2] {k lanes : ℕ}
    (table : Fin (lanes * 2) → Fin k → F) (z : F) :
    packTop (foldTable table z) = foldLane (packTop table) k z := by
  have hs : (lanes * 2 * k) / 2 = lanes * k := by
    rw [Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  apply Array.ext
  · simp [hs]
  · intro i hi hi'
    have hi0 : i < lanes * k := by simpa using hi
    let ij := (topIndex lanes k).symm ⟨i,hi0⟩
    have he : i = ij.1.val * k + ij.2.val := by
      have h := congrArg Fin.val ((topIndex lanes k).apply_symm_apply ⟨i,hi0⟩)
      simpa [ij, topIndex, Nat.add_comm, Nat.mul_comm] using h.symm
    have hiHalf : i < (packTop table).size / 2 := by simpa [hs] using hi0
    suffices hlookup : (packTop (foldTable table z))[i]! =
        (foldLane (packTop table) k z)[i]! by
      simpa only [_root_.getElem!_pos (packTop (foldTable table z)) i hi,
        _root_.getElem!_pos (foldLane (packTop table) k z) i hi'] using hlookup
    rw [he, get_packTop]
    rw [foldLane, ArrayLayout.getElem!_tab _ _ _ (by simpa [← he] using hiHalf)]
    rw [ArrayLayout.foldLane_offset ij.2.isLt]
    have heven : Layout.stackIndex k (2 * ij.1.val) ij.2.val =
        (evenLane ij.1).val * k + ij.2.val := rfl
    have hodd : Layout.stackIndex k (2 * ij.1.val) ij.2.val + k =
        (oddLane ij.1).val * k + ij.2.val := by
      simp only [Layout.stackIndex, oddLane]; ring
    dsimp only
    rw [hodd, heven, get_packTop, get_packTop, foldPair_eq]
    rfl

theorem packLow_fold [Inhabited F] [CharP F 2] {k lanes : ℕ}
    (table : Fin (lanes * 2) → Fin k → F) (z : F) :
    packLow (foldTable table z) = foldLow (packLow table) z := by
  have hs : (lanes * 2 * k) / 2 = lanes * k := by
    rw [Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  apply Array.ext
  · simp [hs]
  · intro i hi hi'
    have hi0 : i < lanes * k := by simpa using hi
    let ij := (lowIndex lanes k).symm ⟨i,hi0⟩
    have he : i = ij.2.val * lanes + ij.1.val := by
      have h := congrArg Fin.val ((lowIndex lanes k).apply_symm_apply ⟨i,hi0⟩)
      simpa [ij, lowIndex, Nat.add_comm, Nat.mul_comm] using h.symm
    have hiHalf : i < (packLow table).size / 2 := by simpa [hs] using hi0
    suffices hlookup : (packLow (foldTable table z))[i]! =
        (foldLow (packLow table) z)[i]! by
      simpa only [_root_.getElem!_pos (packLow (foldTable table z)) i hi,
        _root_.getElem!_pos (foldLow (packLow table) z) i hi'] using hlookup
    rw [he, get_packLow]
    rw [foldLow, ArrayLayout.getElem!_tab _ _ _ (by simpa [← he] using hiHalf)]
    have heven : 2 * (ij.2.val * lanes + ij.1.val) =
        ij.2.val * (lanes * 2) + (evenLane ij.1).val := by
      simp only [evenLane]; ring
    have hodd : 2 * (ij.2.val * lanes + ij.1.val) + 1 =
        ij.2.val * (lanes * 2) + (oddLane ij.1).val := by
      simp only [oddLane]; ring
    rw [hodd, heven, get_packLow, get_packLow, foldPair_eq]
    rfl

/-- Layout-selecting packing; `true` is the initial contiguous-lane layout. -/
def pack (top : Bool) {k lanes : ℕ} (table : Fin lanes → Fin k → F) : Array F :=
  if top then packTop table else packLow table

def foldBlock (top : Bool) (k : ℕ) : ℕ := if top then k else 1

omit [Field F] in
@[simp] theorem size_pack (top : Bool) {k lanes : ℕ} (table : Fin lanes → Fin k → F) :
    (pack top table).size = lanes * k := by cases top <;> simp [pack]

theorem pack_fold [Inhabited F] [CharP F 2] (top : Bool) {k lanes : ℕ}
    (table : Fin (lanes * 2) → Fin k → F) (z : F) :
    pack top (foldTable table z) =
      Protocol.foldValues (pack top table) (foldBlock top k) z := by
  cases top
  · simpa [pack, foldBlock, ReplayRefinement.foldValues_eq_lane,
      ArrayLayout.foldLane_one] using packLow_fold table z
  · simpa [pack, foldBlock, ReplayRefinement.foldValues_eq_lane] using packTop_fold table z

/-- This list is fixed solely by the oracle, threshold and current lane count,
not by the pending message, strategy, weights, claim or future challenge. -/
noncomputable def arrayCandidates [Fintype F] (top : Bool) {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin lanes → I → F)
    (threshold : ℕ) : Finset (Array F) := by
  classical
  exact (candidates enc oracle threshold).image (pack top)

theorem arrayCandidates_size [Fintype F] (top : Bool) {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin lanes → I → F)
    (threshold : ℕ) (a : Array F) (ha : a ∈ arrayCandidates top enc oracle threshold) :
    a.size = lanes * k := by
  classical
  obtain ⟨table, -, rfl⟩ := Finset.mem_image.mp ha
  exact size_pack _ _

/-- The exact lifting interface consumed by `VerifierInvariant.fold_lost`. -/
theorem array_lifts [Fintype F] [Inhabited F] [CharP F 2] (top : Bool)
    {k lanes : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (C : Submodule F (I → F)) (range_eq : LinearMap.range enc = C)
    (oracle : Fin (lanes * 2) → I → F) (threshold : ℕ) (z : F)
    (good : ¬ RowBad foldGenerator C threshold
      ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)] z) :
    ∀ folded ∈ arrayCandidates top enc (foldOracle oracle z) threshold,
      ∃ witness ∈ arrayCandidates top enc oracle threshold,
        folded = Protocol.foldValues witness (foldBlock top k) z := by
  classical
  intro folded hfolded
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hfolded
  obtain ⟨p, hp, rfl⟩ := coefficient_lifts enc C range_eq oracle threshold z good v hv
  exact ⟨pack top p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, pack_fold top p z⟩

/-- Instantiated novel-code lifting, with no assumed encoder/RS identity.
The only excluded seeds are the explicit same-set RowBad event. -/
theorem novel_array_lifts [Fintype F] [Inhabited F] [CharP F 2] (top : Bool)
    (basis : ℕ → F) (n : ℕ) (independent : AdditiveCode.Independent basis n)
    (domain : I → F) {lanes : ℕ} (oracle : Fin (lanes * 2) → I → F)
    (threshold : ℕ) (z : F)
    (good : ¬ RowBad foldGenerator (rsCode domain (2^n)) threshold
      ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)] z) :
    ∀ folded ∈ arrayCandidates top (novelEncoder basis n domain)
        (foldOracle oracle z) threshold,
      ∃ witness ∈ arrayCandidates top (novelEncoder basis n domain) oracle threshold,
        folded = Protocol.foldValues witness (foldBlock top (2^n)) z :=
  array_lifts top _ _ (novelEncoder_range basis n independent domain) oracle threshold z good

/-- The arbitrary column-major oracle is folded with the executable adjacent
array helper, rather than replaced by a separate correlated-agreement model. -/
theorem foldOracle_column [Inhabited F] [CharP F 2] {lanes : ℕ}
    (oracle : Fin (lanes * 2) → I → F) (z : F) (i : I) :
    Array.ofFn (fun lane => foldOracle oracle z lane i) =
      foldLow (Array.ofFn (fun lane => oracle lane i)) z := by
  apply Array.ext
  · simp
  · intro j hj hj'
    have hjl : j < lanes := by simpa using hj
    have he : 2*j < lanes*2 := by omega
    have ho : 2*j+1 < lanes*2 := by omega
    simp [foldLow, tab, getElem!_pos, he, ho, foldOracle, evenLane, oddLane, foldPair_eq]

/-- The concrete dense encoder is exactly this linear map on its mapped
coefficient array, at every bounded machine query. -/
theorem novelEncoder_encode [Inhabited F]
    (f : AdditiveCode.BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate : ℕ) (a : Array E) (shape : a.size = 2^n)
    (q : Fin (2^(n+rate))) :
    novelEncoder (AdditiveCode.bitBasis f.map) n
      (fun q : Fin (2^(n+rate)) => f.map (UInt64.ofNat q.val))
      (fun j => e.map a[j.val]!) q = e.map (encode n rate a)[q.val]! :=
  (AdditiveCode.encode_map f e ofK n rate a shape q.val q.isLt).symm

/-- Machine basis independence is discharged from the checked word
representation; the caller supplies neither an RS equality nor a basis axiom. -/
theorem machineEncoder_range [Inhabited F] [CharP F 2]
    (f : AdditiveCode.BaseRepresentation F) (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate : ℕ) (depth : n+rate ≤ 64) :
    LinearMap.range (novelEncoder (AdditiveCode.bitBasis f.map) n
      (fun q : Fin (2^(n+rate)) => f.map (UInt64.ofNat q.val))) =
      rsCode (AdditiveCode.machineDomain f
        (AdditiveCode.baseRepresentation_injective f e ofK) (n+rate) depth) (2^n) :=
  novelEncoder_range _ _ (AdditiveCode.bitBasis_independent f
    (AdditiveCode.baseRepresentation_injective f e ofK) n (by omega)) _

open Classical in
/-- The novel encoder uses exactly the coefficient-table RS code employed by
the Johnson/list-size development, not a second notion of polynomial code. -/
theorem novelEncoder_monomial_coefficients [CharP F 2]
    (basis : ℕ → F) (n : ℕ) (independent : AdditiveCode.Independent basis n)
    (domain : I → F) (table : Fin (2^n) → F) :
    ∃ coefficients : Fin (2^n) → F, ∀ i,
      (Polynomial.ofFn (2^n) coefficients).eval (domain i) =
        novelEncoder basis n domain table i := by
  apply (mem_rsCode_iff_coefficients _ _ _).mp
  rw [← novelEncoder_range basis n independent domain]
  exact LinearMap.mem_range_self _ _

/-- Correct physical shape for either branch of `foldValues`. -/
theorem arrayCandidates_round_shape [Fintype F] (top : Bool) {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin (lanes * 2) → I → F)
    (threshold : ℕ) (a : Array F) (ha : a ∈ arrayCandidates top enc oracle threshold) :
    a.size = ((if top then lanes else lanes*k) * 2) * foldBlock top k := by
  rw [arrayCandidates_size top enc oracle threshold a ha]
  cases top <;> simp [foldBlock]
  ring

/-- Checked MCA provider for the proved novel code. The exceptional set is
derived, not assumed: its exact BCHKS numerator is independent of lane count.
Every surviving new array candidate lifts to the commitment-fixed old list. -/
theorem novel_candidate_provider [Fintype F] [Inhabited F] [CharP F 2]
    (top : Bool) (basis : ℕ → F) (n : ℕ)
    (independent : AdditiveCode.Independent basis n)
    {N lanes : ℕ} (domain : Fin N ↪ F)
    (degree_pos : 1 ≤ 2^n-1) (degree_bound : 2^n-1 ≤ N-2)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (johnson : radius < 1 - Real.sqrt (((2^n-1 : ℕ) : ℝ) / N))
    (oracle : Fin (lanes * 2) → Fin N → F) :
    ∃ bad : Finset F,
      (Soundness.uniformProb bad : ℝ) ≤
        johnsonNumerator N (2^n) radius / Fintype.card F ∧
      ∀ z ∉ bad, ∀ folded ∈
        arrayCandidates top (novelEncoder basis n domain) (foldOracle oracle z)
          ⌈(N : ℝ) * (1-radius)⌉₊,
        ∃ witness ∈ arrayCandidates top (novelEncoder basis n domain) oracle
            ⌈(N : ℝ) * (1-radius)⌉₊,
          folded = Protocol.foldValues witness (foldBlock top (2^n)) z := by
  classical
  let U : Fin 2 → Fin lanes → Fin N → F :=
    ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)]
  let bad := Finset.univ.filter (RowBad foldGenerator (rsCode domain (2^n))
    ⌈(N : ℝ) * (1-radius)⌉₊ U)
  have hd : (2^n : ℕ)-1+1 = 2^n := by omega
  refine ⟨bad, ?_, ?_⟩
  · simpa only [hd] using johnson_row_bad_probability domain degree_pos degree_bound
      radius radius_nonneg johnson U
  · intro z hz
    exact novel_array_lifts top basis n independent domain oracle _ z
      (by simpa [bad, U] using hz)

/-- Final machine-domain provider. Binary-basis independence, distinct machine
indices, exact RS identification and the MCA estimate are all proved internally.
Representation parameters concern primitive machine operations only. -/
theorem machine_candidate_provider [Fintype F] [Inhabited F] [CharP F 2]
    (top : Bool) (f : AdditiveCode.BaseRepresentation F)
    (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate : ℕ) (depth : n+rate ≤ 64) {lanes : ℕ}
    (degree_pos : 1 ≤ 2^n-1) (degree_bound : 2^n-1 ≤ 2^(n+rate)-2)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (johnson : radius < 1 - Real.sqrt (((2^n-1 : ℕ) : ℝ) / 2^(n+rate)))
    (oracle : Fin (lanes * 2) → Fin (2^(n+rate)) → F) :
    let enc := novelEncoder (AdditiveCode.bitBasis f.map) n
      (fun q : Fin (2^(n+rate)) => f.map (UInt64.ofNat q.val))
    let threshold := ⌈((2^(n+rate) : ℕ) : ℝ) * (1-radius)⌉₊
    ∃ bad : Finset F,
      (Soundness.uniformProb bad : ℝ) ≤
        johnsonNumerator (2^(n+rate)) (2^n) radius / Fintype.card F ∧
      ∀ z ∉ bad, ∀ folded ∈ arrayCandidates top enc (foldOracle oracle z) threshold,
        ∃ witness ∈ arrayCandidates top enc oracle threshold,
          folded = Protocol.foldValues witness (foldBlock top (2^n)) z := by
  have hf := AdditiveCode.baseRepresentation_injective f e ofK
  exact novel_candidate_provider top (AdditiveCode.bitBasis f.map) n
    (AdditiveCode.bitBasis_independent f hf n (by omega))
    (AdditiveCode.machineDomain f hf (n+rate) depth)
    degree_pos degree_bound radius radius_nonneg (by simpa using johnson) oracle

/-- Total coefficient extraction at the bounded physical matrix indices. -/
def unpack [Inhabited F] (top : Bool) (lanes k : ℕ) (a : Array F) :
    Fin lanes → Fin k → F :=
  fun lane j => a[(if top then topIndex lanes k else lowIndex lanes k) (lane,j) |>.val]!

omit [Field F] in
theorem unpack_pack [Inhabited F] (top : Bool) {lanes k : ℕ}
    (table : Fin lanes → Fin k → F) :
    unpack top lanes k (pack top table) = table := by
  funext lane j
  cases top <;> simp [unpack, pack, packTop, packLow]

omit [Field F] in
theorem pack_unpack [Inhabited F] (top : Bool) {lanes k : ℕ}
    (a : Array F) (shape : a.size = lanes*k) :
    pack top (unpack top lanes k a) = a := by
  apply Array.ext
  · simpa using shape.symm
  · intro i hi hi'
    cases top <;>
      simp [pack, packTop, packLow, unpack, _root_.getElem!_pos a i hi']

/-- Every exact-size array is represented; candidate coverage is a theorem,
not a decoder assumption or one-way image inclusion. -/
theorem arrayCandidates_mem_iff [Fintype F] [Inhabited F] (top : Bool) {k lanes : ℕ}
    (enc : (Fin k → F) →ₗ[F] (I → F)) (oracle : Fin lanes → I → F)
    (threshold : ℕ) (a : Array F) :
    a ∈ arrayCandidates top enc oracle threshold ↔
      a.size = lanes*k ∧ Agrees enc oracle threshold (unpack top lanes k a) := by
  classical
  constructor
  · intro ha
    obtain ⟨table, htable, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨size_pack _ _, by
      rw [unpack_pack]
      exact (mem_candidates _ _ _ _).mp htable⟩
  · rintro ⟨shape, hagree⟩
    exact Finset.mem_image.mpr ⟨unpack top lanes k a,
      (mem_candidates _ _ _ _).mpr hagree, pack_unpack top a shape⟩

omit [Field F] in
theorem unpack_one [Inhabited F] (top : Bool) (k : ℕ) (a : Array F) (j : Fin k) :
    unpack top 1 k a 0 j = a[j.val]! := by
  cases top <;> simp [unpack, topIndex, lowIndex]

open Classical in
/-- One remaining lane is exactly the ordinary row-encoding agreement list,
for every physical array of the right size. -/
theorem oneLane_arrayCandidates_mem_iff [Fintype F] [Fintype I] [Inhabited F]
    (top : Bool) {k : ℕ} (enc : (Fin k → F) →ₗ[F] (I → F))
    (word : I → F) (threshold : ℕ) (a : Array F) :
    a ∈ arrayCandidates top enc (fun _ : Fin 1 => word) threshold ↔
      a.size = k ∧ threshold ≤
        (Finset.univ.filter fun i => enc (fun j => a[j.val]!) i = word i).card := by
  rw [arrayCandidates_mem_iff]
  simp only [one_mul]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨T, hT, hagree⟩
    apply hT.trans
    apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [show unpack top 1 k a 0 = (fun j => a[j.val]!) from
      funext (unpack_one top k a)] using hagree 0 i hi
  · intro hcard
    refine ⟨_, hcard, ?_⟩
    intro lane i hi
    fin_cases lane
    change enc (unpack top 1 k a 0) i = word i
    simpa only [show unpack top 1 k a 0 = (fun j => a[j.val]!) from
      funext (unpack_one top k a)] using (Finset.mem_filter.mp hi).2

open Classical in
/-- Every actual coefficient array with enough exact encoded matches belongs
to the one-lane list after mapping primitive machine operations into the field. -/
theorem oneLane_encode_coverage [Fintype F] [Inhabited F]
    (top : Bool) (f : AdditiveCode.BaseRepresentation F)
    (e : QueryRefinement.Representation F)
    (ofK : ∀ s, e.map (E.ofK s) = f.map s)
    (n rate threshold : ℕ) (a : Array E) (shape : a.size = 2^n)
    (word : Fin (2^(n+rate)) → E)
    (hmatches : threshold ≤
      (Finset.univ.filter fun q => (encode n rate a)[q.val]! = word q).card) :
    a.map e.map ∈ arrayCandidates top
      (novelEncoder (AdditiveCode.bitBasis f.map) n
        (fun q : Fin (2^(n+rate)) => f.map (UInt64.ofNat q.val)))
      (fun _ : Fin 1 => fun q => e.map (word q)) threshold := by
  apply (oneLane_arrayCandidates_mem_iff _ _ _ _ _).mpr
  refine ⟨by simpa using shape, hmatches.trans (Finset.card_le_card ?_)⟩
  intro q hq
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hcoeff : (fun j : Fin (2^n) => (a.map e.map)[j.val]!) =
      (fun j : Fin (2^n) => e.map a[j.val]!) := by
    funext j
    have hj : j.val < a.size := by rw [shape]; exact j.isLt
    simp [_root_.getElem!_pos, hj]
  rw [hcoeff, novelEncoder_encode f e ofK n rate a shape q, (Finset.mem_filter.mp hq).2]

/-- The actual field's actual dense row encoder as a linear map. -/
noncomputable def concreteEncoder (n rate : ℕ) :
    (Fin (2^n) → E) →ₗ[E] (Fin (2^(n+rate)) → E) :=
  novelEncoder (AdditiveCode.bitBasis E.ofK) n
    (fun q => E.ofK (UInt64.ofNat q.val))

open Classical in
/-- Exact one-lane candidate membership for executable `encode`. This gives
the direct actual close invariant from `Lost`, with no coverage assumption. -/
theorem concrete_oneLane_mem_iff (top : Bool) (n rate threshold : ℕ)
    (word : Fin (2^(n+rate)) → E) (a : Array E) :
    a ∈ arrayCandidates top (concreteEncoder n rate) (fun _ : Fin 1 => word) threshold ↔
      a.size = 2^n ∧ threshold ≤
        (Finset.univ.filter fun q => (encode n rate a)[q.val]! = word q).card := by
  rw [oneLane_arrayCandidates_mem_iff]
  apply and_congr_right
  intro shape
  have heq (q : Fin (2^(n+rate))) :
      concreteEncoder n rate (fun j => a[j.val]!) q = (encode n rate a)[q.val]! :=
    (AdditiveCode.concrete_encode_eval n rate a shape q.val q.isLt).symm
  simp only [heq]

/-- Fully concrete PCS folding provider: actual E, actual dense encoder and
actual executable array folds, with no field-representation or MCA premise. -/
theorem concrete_candidate_provider (top : Bool) (n rate : ℕ)
    (depth : n+rate ≤ 64) {lanes : ℕ}
    (degree_pos : 1 ≤ 2^n-1) (degree_bound : 2^n-1 ≤ 2^(n+rate)-2)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (johnson : radius < 1 - Real.sqrt (((2^n-1 : ℕ) : ℝ) / 2^(n+rate)))
    (oracle : Fin (lanes * 2) → Fin (2^(n+rate)) → E) :
    let threshold := ⌈((2^(n+rate) : ℕ) : ℝ) * (1-radius)⌉₊
    ∃ bad : Finset E,
      (Soundness.uniformProb bad : ℝ) ≤
        johnsonNumerator (2^(n+rate)) (2^n) radius / Fintype.card E ∧
      ∀ z ∉ bad, ∀ folded ∈
          arrayCandidates top (concreteEncoder n rate) (foldOracle oracle z) threshold,
        ∃ witness ∈ arrayCandidates top (concreteEncoder n rate) oracle threshold,
          folded = Protocol.foldValues witness (foldBlock top (2^n)) z :=
  machine_candidate_provider top AdditiveCode.concreteBaseRepresentation
    QueryRefinement.concreteRepresentation (fun _ => rfl) n rate depth degree_pos
    degree_bound radius radius_nonneg johnson oracle

end Whir.CandidateFolding
