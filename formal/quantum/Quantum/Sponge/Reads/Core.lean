module

public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Oracle.Compressed.Measurement
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

@[expose] public section

/-!
# Classical reads after a quantum program

A program `x` runs, and at its leaf a classical oracle algorithm `oa` (an `OracleComp`, possibly
adaptive) is run on the final register, each of its queries answered by a basis call
(`Quantum.QComp.callBasis`). `loggedReads` records the queries and answers, and `withReads x rd oa`
appends these logged reads to every leaf of `x`.

Against a runtime whose private register holds a classical table read by `ans`, and whose basis
calls are the projections onto the tables giving the read answer (`readProjector`), the logged
reads have branch at `(b, log)` the projection onto the tables consistent with `log`
(`logProjector`), and zero unless `log` is a transcript of `oa` returning `b` (`IsTranscript`).
-/

open Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ENNReal

universe u v u₁ v₁ w

namespace Quantum.Sponge

open Quantum

/-! ## Logged reads -/

section logged

variable {ι : Type} {ospec : OracleSpec.{0, 0} ι} {β : Type}

/-- `r = (b, log)` is a run of `oa`: answering the queries of `oa` in turn with the answers of
`log`, whose queries are those of `oa`, ends with `b` exactly when `log` is used up. -/
def IsTranscript : OracleComp ospec β → β × QueryLog ospec → Prop :=
  OracleComp.construct (C := fun _ ↦ β × QueryLog ospec → Prop)
    (fun b r ↦ r = (b, []))
    (fun t _ ih r ↦ ∃ c log, r.2 = ⟨t, c⟩ :: log ∧ ih c (r.1, log))

theorem isTranscript_pure (b : β) (r : β × QueryLog ospec) :
    IsTranscript (pure b : OracleComp ospec β) r ↔ r = (b, []) :=
  Iff.rfl

theorem isTranscript_query_bind (t : ι) (k : ospec t → OracleComp ospec β)
    (r : β × QueryLog ospec) :
    IsTranscript (liftM (ospec.query t) >>= k) r ↔
      ∃ c log, r.2 = ⟨t, c⟩ :: log ∧ IsTranscript (k c) (r.1, log) :=
  Iff.rfl

/-- A transcript of an algorithm making at most `n` queries satisfying `p` logs at most `n`
such queries. -/
theorem IsTranscript.countP_le {p : ι → Prop} [DecidablePred p] {oa : OracleComp ospec β}
    {n : ℕ} (hb : IsQueryBoundP oa p n) {r : β × QueryLog ospec} (hr : IsTranscript oa r) :
    r.2.countP (fun e ↦ decide (p e.1)) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure b =>
    rw [isTranscript_pure] at hr
    subst hr
    simp
  | query_bind t k ih =>
    obtain ⟨c, log, hlog, hk⟩ := (isTranscript_query_bind t k r).mp hr
    rw [isQueryBoundP_query_bind_iff] at hb
    have h := ih c (hb.2 c) hk
    rw [hlog, List.countP_cons]
    by_cases ht : p t
    · have hn : 0 < n := hb.1.resolve_left (not_not.mpr ht)
      simp only [ht, ↓reduceIte, decide_true] at h ⊢
      omega
    · simpa [ht] using h

variable {spec : QuantumOracleSpec.{u₁, v₁}} {B : QReg}

/-- Run `oa` on the held register `B`, answering each query `t` with the program `rd t`, and
return its result with the log of its queries and answers, in the order they were made. -/
noncomputable def loggedReads (rd : QueryImpl ospec (QComp spec B B)) :
    OracleComp ospec β → QComp spec B B (β × QueryLog ospec) :=
  OracleComp.construct (C := fun _ ↦ QComp spec B B (β × QueryLog ospec))
    (fun b ↦ QuantumComp₂.pure (b, []))
    (fun t _ ih ↦ (rd t).bind fun c ↦ (ih c).bind fun r ↦ QuantumComp₂.pure (r.1, ⟨t, c⟩ :: r.2))

theorem loggedReads_pure (rd : QueryImpl ospec (QComp spec B B)) (b : β) :
    loggedReads rd (pure b : OracleComp ospec β) = QuantumComp₂.pure (b, []) :=
  rfl

theorem loggedReads_query_bind (rd : QueryImpl ospec (QComp spec B B)) (t : ι)
    (k : ospec t → OracleComp ospec β) :
    loggedReads rd (liftM (ospec.query t) >>= k) =
      (rd t).bind fun c ↦ (loggedReads rd (k c)).bind fun r ↦
        QuantumComp₂.pure (r.1, ⟨t, c⟩ :: r.2) :=
  rfl

end logged

/-! ## The branches of logged reads against a table register -/

section branch

variable {ι : Type} {ospec : OracleSpec.{0, 0} ι} [∀ t, DecidableEq (ospec t)] {β : Type}
  {T : Type} [Fintype T] [DecidableEq T]

/-- The projection onto the tables whose answer to the query `t` is `c`. -/
noncomputable def readProjector (ans : T → (t : ι) → ospec t) (t : ι) (c : ospec t) :
    Matrix T T ℂ :=
  diagonal fun τ ↦ if ans τ t = c then 1 else 0

/-- The projection onto the tables consistent with every entry of `log`. -/
noncomputable def logProjector (ans : T → (t : ι) → ospec t) (log : QueryLog ospec) :
    Matrix T T ℂ :=
  diagonal fun τ ↦ if ∀ e ∈ log, ans τ e.1 = e.2 then 1 else 0

omit [Fintype T] in
theorem conjTranspose_logProjector (ans : T → (t : ι) → ospec t) (log : QueryLog ospec) :
    (logProjector ans log)ᴴ = logProjector ans log := by
  rw [logProjector, diagonal_conjTranspose]
  congr 1
  funext τ
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem logProjector_mul_self (ans : T → (t : ι) → ospec t) (log : QueryLog ospec) :
    logProjector ans log * logProjector ans log = logProjector ans log := by
  rw [logProjector, diagonal_mul_diagonal]
  congr 1
  funext τ
  split_ifs <;> simp

omit [Fintype T] in
theorem logProjector_nil (ans : T → (t : ι) → ospec t) :
    logProjector ans ([] : QueryLog ospec) = 1 := by
  simp [logProjector]

theorem logProjector_cons (ans : T → (t : ι) → ospec t) (t : ι) (c : ospec t)
    (log : QueryLog ospec) :
    logProjector ans (⟨t, c⟩ :: log) = logProjector ans log * readProjector ans t c := by
  rw [logProjector, logProjector, readProjector, diagonal_mul_diagonal]
  congr 1
  funext τ
  by_cases h₁ : ans τ t = c <;> by_cases h₂ : ∀ e ∈ log, ans τ e.1 = e.2 <;>
    simp [h₁, h₂]

omit [∀ t, DecidableEq (ospec t)] [Fintype T] [DecidableEq T] in
theorem sigma_mk_eq_mk_iff {t : ι} {c c' : ospec t} :
    (⟨t, c⟩ : (t : ι) × ospec t) = ⟨t, c'⟩ ↔ c = c' := by
  simp

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

open scoped Classical in
/-- **The branches of logged reads.** If every basis call `rd B t` against `R` reporting `c` is the
projection onto the tables answering `c`, the logged reads of `oa` reporting `(b, log)` are the
projection onto the tables consistent with `log` when `(b, log)` is a transcript of `oa`, and
zero otherwise. -/
theorem branch_run₂_loggedReads (ans : R.D → (t : ι) → ospec t)
    (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (hrd : ∀ B t c, (R.run₂ .instruments (rd B t)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ readProjector ans t c))
    (B : QReg) (oa : OracleComp ospec β) (r : β × QueryLog ospec) :
    (R.run₂ .instruments (loggedReads (rd B) oa)).branch r =
      if IsTranscript oa r then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ logProjector ans r.2)
      else 0 := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure b =>
    rw [loggedReads_pure, QuantumRuntime.run₂_pure, isTranscript_pure]
    by_cases h : r = (b, [])
    · subst h
      rw [SubInstrument.branch_pure_self, ite_eq_left rfl, logProjector_nil, one_kronecker_one,
        MatrixMap.conj_one]
    · rw [SubInstrument.branch_pure_of_ne h, ite_eq_right h]
  | query_bind t k ih =>
    obtain ⟨b, log₀⟩ := r
    refine LinearMap.ext fun ρ ↦ ?_
    rw [loggedReads_query_bind, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
    simp only [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_pure,
      DSubInstrument.branch_bind_apply]
    have hzero (c : ospec t) (r : β × QueryLog ospec) (hr : (r.1, ⟨t, c⟩ :: r.2) ≠ (b, log₀))
        (σ : Matrix (B × R.D) (B × R.D) ℂ) :
        (SubInstrument.pure (r.1, (⟨t, c⟩ :: r.2 : QueryLog ospec)) :
          SubInstrument (B × R.D) (B × R.D) _).branch (b, log₀) σ = 0 := by
      rw [SubInstrument.branch_pure_of_ne (Ne.symm hr)]
      rfl
    by_cases hlog : ∃ c log, log₀ = ⟨t, c⟩ :: log
    · obtain ⟨c₀, log, rfl⟩ := hlog
      have hT : IsTranscript (liftM (ospec.query t) >>= k) (b, ⟨t, c₀⟩ :: log) ↔
          IsTranscript (k c₀) (b, log) := by
        rw [isTranscript_query_bind]
        constructor
        · rintro ⟨c, log', h, hk⟩
          obtain ⟨h₁, rfl⟩ := List.cons_eq_cons.mp h
          obtain rfl := sigma_mk_eq_mk_iff.mp h₁.symm
          exact hk
        · exact fun h ↦ ⟨c₀, log, rfl, h⟩
      rw [tsum_eq_single c₀ fun c hc ↦ ?_]
      · rw [tsum_eq_single (b, log) fun r hr ↦ hzero _ _ ?_ _]
        · rw [SubInstrument.branch_pure_self, LinearMap.id_apply, ih, hrd]
          by_cases hk : IsTranscript (k c₀) (b, log)
          · rw [ite_eq_left hk, ite_eq_left (hT.mpr hk), logProjector_cons, ← Matrix.one_mul (1 : Matrix B B ℂ),
              mul_kronecker_mul, MatrixMap.conj_mul, LinearMap.comp_apply, Matrix.one_mul]
          · rw [ite_eq_right hk, ite_eq_right (mt hT.mp hk)]
            rfl
        · intro h
          obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp h
          exact hr (Prod.ext h₁ (List.cons_eq_cons.mp h₂).2)
      · refine (tsum_congr fun r ↦ hzero _ _ ?_ _).trans tsum_zero
        intro h
        obtain ⟨-, h₂⟩ := Prod.ext_iff.mp h
        exact hc (sigma_mk_eq_mk_iff.mp (List.cons_eq_cons.mp h₂).1)
    · have hT : ¬ IsTranscript (liftM (ospec.query t) >>= k) (b, log₀) := by
        rw [isTranscript_query_bind]
        rintro ⟨c, log, h, -⟩
        exact hlog ⟨c, log, h⟩
      rw [ite_eq_right hT]
      refine (tsum_congr fun c ↦ (tsum_congr fun r ↦ hzero _ _ ?_ _).trans tsum_zero).trans
        tsum_zero
      intro h
      exact hlog ⟨c, r.2, (Prod.ext_iff.mp h).2.symm⟩

omit [∀ t, DecidableEq (ospec t)] in
/-- A linear map fixing every term of a sum fixes the sum. -/
theorem map_tsum_of_forall_eq {κ n : Type*} [Fintype n] (Φ : MatrixMap n n)
    (a : κ → Matrix n n ℂ) (h : ∀ k, Φ (a k) = a k) : Φ (∑' k, a k) = ∑' k, a k := by
  by_cases hs : Summable a
  · rw [← LinearMap.coe_toContinuousLinearMap' Φ, ContinuousLinearMap.map_tsum _ hs]
    exact tsum_congr fun k ↦ h k
  · rw [tsum_eq_zero_of_not_summable hs, map_zero]

/-- A program on a fixed final register, read as a general program. -/
def _root_.Quantum.QComp.toComp {B : QReg} {γ : Type} (c : QComp spec B B γ) :
    QuantumComp LocalSig.instruments.{0} spec (QuantumComp₂.Leaf B γ) B :=
  c

variable {W : QReg → Type} {A : QReg}

/-- **Classical reads after a program.** Run `x`; at its leaf `w` on the register `u`, run the
classical algorithm `oa ⟨u, w⟩` on `u`, its queries answered by `rd u`, and keep `w` with the
result and the log of the reads. -/
noncomputable def withReads (x : QuantumComp LocalSig.instruments.{0} spec W A)
    (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (oa : (Σ u, W u) → OracleComp ospec β) :
    QuantumComp LocalSig.instruments.{0} spec (fun u ↦ W u × β × QueryLog ospec) A :=
  x.bind fun u w ↦ QuantumComp.bind (loggedReads (rd u) (oa ⟨u, w⟩)).toComp fun _ l ↦
    QuantumComp.pure (cast (congrArg W l.1.symm) w, l.2)

omit [∀ t, DecidableEq (ospec t)] in
/-- A Kraus map of a projector is idempotent. -/
theorem conj_comp_conj_of_mul_self {n : Type*} [Fintype n] {K : Matrix n n ℂ} (hK : K * K = K) :
    MatrixMap.conj K ∘ₗ MatrixMap.conj K = MatrixMap.conj K := by
  rw [← MatrixMap.conj_mul, hK]

open scoped Classical in
/-- **The reads are recorded in the table register.** Against a runtime as in
`branch_run₂_loggedReads`, every branch of `withReads x rd oa` at a leaf with log `log` is
supported on the tables consistent with `log`, and is zero unless the leaf's result and log are
a transcript of the reads. -/
theorem branch_run_withReads (ans : R.D → (t : ι) → ospec t)
    (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (hrd : ∀ B t c, (R.run₂ .instruments (rd B t)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ readProjector ans t c))
    (x : QuantumComp LocalSig.instruments.{0} spec W A) (oa : (Σ u, W u) → OracleComp ospec β)
    (q : Σ u, W u × β × QueryLog ospec) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (if IsTranscript (oa ⟨q.1, q.2.1⟩) q.2.2 then
        MatrixMap.conj ((1 : Matrix q.1 q.1 ℂ) ⊗ₖ logProjector ans q.2.2.2) else 0)
      ((R.run .instruments (withReads x rd oa)).branch q ρ) =
      (R.run .instruments (withReads x rd oa)).branch q ρ := by
  set Φ : MatrixMap (q.1 × R.D) (q.1 × R.D) := if IsTranscript (oa ⟨q.1, q.2.1⟩) q.2.2 then
    MatrixMap.conj ((1 : Matrix q.1 q.1 ℂ) ⊗ₖ logProjector ans q.2.2.2) else 0 with hΦ
  have hΦΦ : Φ ∘ₗ Φ = Φ := by
    rw [hΦ]
    split_ifs
    · refine conj_comp_conj_of_mul_self ?_
      rw [← mul_kronecker_mul, Matrix.one_mul, logProjector_mul_self]
    · rfl
  rw [withReads, QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  refine map_tsum_of_forall_eq Φ _ fun p ↦ ?_
  obtain ⟨u, w⟩ := p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  refine map_tsum_of_forall_eq Φ _ fun l ↦ ?_
  obtain ⟨v, hv, r⟩ := l
  obtain rfl : v = u := hv
  rw [QuantumRuntime.run_pure]
  dsimp only
  simp only [cast_eq]
  by_cases hq : q = ⟨v, (w, r)⟩
  · subst hq
    rw [DSubInstrument.branch_ret_self, LinearMap.id_apply]
    change Φ ((R.run₂ .instruments (loggedReads (rd v) (oa ⟨v, w⟩))).branch r _) =
      (R.run₂ .instruments (loggedReads (rd v) (oa ⟨v, w⟩))).branch r _
    rw [branch_run₂_loggedReads R ans rd hrd, hΦ]
    split_ifs
    · rw [← LinearMap.comp_apply, conj_comp_conj_of_mul_self]
      rw [← mul_kronecker_mul, Matrix.one_mul, logProjector_mul_self]
    · rfl
  · rw [DSubInstrument.branch_ret_of_ne _ hq, LinearMap.zero_apply, map_zero]

variable {B : QReg}

omit [∀ t, DecidableEq (ospec t)] in
/-- **The budget of logged reads.** If each read of `t` makes one call of `port t`, and `oa` makes
at most `b i` queries with port `i` on every path, the logged reads are within the budget `b`. -/
theorem isQueryBound_loggedReads [DecidableEq spec.Port] (port : ι → spec.Port)
    (rd : QueryImpl ospec (QComp spec B B))
    (hrd : ∀ t, (rd t).IsQueryBound (Pi.single (port t) 1)) (oa : OracleComp ospec β)
    (b : spec.Port → ℕ) (hb : ∀ i, IsQueryBoundP oa (fun t ↦ port t = i) (b i)) :
    (loggedReads rd oa).IsQueryBound b := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure a => exact QuantumComp₂.isQueryBound_pure _ _
  | query_bind t k ih =>
    rw [loggedReads_query_bind]
    have hb' := fun i ↦ (isQueryBoundP_query_bind_iff _ t k (b i)).mp (hb i)
    refine (QuantumComp₂.isQueryBound_bind (hrd t) fun c ↦
      QuantumComp₂.isQueryBound_bind (ih c (fun i ↦ if port t = i then b i - 1 else b i)
        fun i ↦ (hb' i).2 c) fun _ ↦ QuantumComp₂.isQueryBound_pure _ 0).mono fun i ↦ ?_
    have hpos := (hb' (port t)).1.resolve_left (not_not.mpr rfl)
    by_cases hi : port t = i
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same, ↓reduceIte, add_zero]
      omega
    · simp [hi, Ne.symm hi]

omit [∀ t, DecidableEq (ospec t)] in
/-- **The budget of a program followed by reads**: the budget of the program plus that of the
reads. -/
theorem isQueryBound_withReads [DecidableEq spec.Port] {W : QReg → Type} {A : QReg}
    (port : ι → spec.Port) (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (hrd : ∀ B t, (rd B t).IsQueryBound (Pi.single (port t) 1))
    {x : QuantumComp LocalSig.instruments.{0} spec W A} {b₁ : spec.Port → ℕ}
    (hx : x.IsQueryBound b₁) (oa : (Σ u, W u) → OracleComp ospec β) (b₂ : spec.Port → ℕ)
    (hb : ∀ p i, IsQueryBoundP (oa p) (fun t ↦ port t = i) (b₂ i)) :
    (withReads x rd oa).IsQueryBound (b₁ + b₂) :=
  hx.bind fun u w ↦ ((isQueryBound_loggedReads port (rd u) (hrd u) (oa ⟨u, w⟩) b₂ (hb _)).bind
    (b₂ := 0) fun _ _ ↦ QuantumComp.isQueryBound_pure _ _).mono (add_zero b₂).le

end branch

/-! ## Measuring the private register -/

section jointLaw

/-- `1 ⊗ |d⟩⟨d|` is a projector. -/
theorem one_kronecker_single_conjTranspose_mul_self {M D : Type*} [Fintype M] [DecidableEq M]
    [Fintype D] [DecidableEq D] (d : D) :
    ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ))ᴴ *
        ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ)) =
      (1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ) := by
  rw [conjTranspose_kronecker, conjTranspose_one, Matrix.conjTranspose_single, star_one,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.single_mul_single_same, mul_one]

/-- The projections `1 ⊗ |d⟩⟨d|` onto the basis states of the second factor are complete. -/
theorem sum_one_kronecker_single_mul_self (M D : Type*) [Fintype M] [DecidableEq M] [Fintype D]
    [DecidableEq D] :
    ∑ d : D, ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ))ᴴ *
      ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ)) = 1 := by
  rw [Finset.sum_congr rfl fun d _ ↦ one_kronecker_single_conjTranspose_mul_self d]
  ext ⟨m, d⟩ ⟨m', d'⟩
  by_cases hm : m = m' <;>
    simp [Matrix.sum_apply, Matrix.one_apply, Matrix.single_apply, ite_and, hm]

/-- Measuring the second factor of `M × D` in the computational basis, reporting `d`. -/
noncomputable def measureReg (M D : Type*) [Fintype M] [DecidableEq M] [Fintype D]
    [DecidableEq D] : SubInstrument (M × D) (M × D) D :=
  SubInstrument.ofKraus (fun d ↦ (1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ))
    (sum_one_kronecker_single_mul_self M D)

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w}
  {A : QReg}

/-- **The joint law of a leaf and the measured private register.** Run `x` against `R` from
`ρ ⊗ init`; at the leaf `p`, measure the private register in the computational basis and observe
`f p d` for the reported basis state `d`. -/
noncomputable def jointLaw {γ : Type*} [MeasurableSpace γ] (R : QuantumRuntime spec)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A) (f : (Σ u, W u) → R.D → γ) :
    Measure γ :=
  Measure.sum fun p ↦ ((measureReg p.1 R.D).map (f p)).outcomeMeasure (R.jointPost I x ρ p)

/-- The diagonal projectors onto the basis states with a property sum to the diagonal projector
onto the property. -/
theorem sum_ite_one_kronecker_single {M D : Type*} [Fintype M] [DecidableEq M] [Fintype D]
    [DecidableEq D] (g : D → Bool) :
    ∑ d : D, (if g d then (1 : Matrix M M ℂ) ⊗ₖ Matrix.single d d (1 : ℂ) else 0) =
      (1 : Matrix M M ℂ) ⊗ₖ diagonal fun d ↦ if g d then 1 else 0 := by
  rw [← Finset.sum_filter]
  ext ⟨m, d⟩ ⟨m', d'⟩
  rw [Matrix.sum_apply]
  by_cases hd : d = d'
  · subst hd
    by_cases hg : g d <;> simp [kroneckerMap_apply, Matrix.single_apply, hg]
  · simp only [kroneckerMap_apply, Matrix.single_apply]
    simp [hd]
    exact Or.inl fun x _ h₁ h₂ ↦ hd (h₁.symm.trans h₂)

/-- The probability of an event observed jointly with the measured private register: at each
leaf, the weight of the joint post-state on the diagonal projector onto the event. -/
theorem jointLaw_apply_true (R : QuantumRuntime spec) (I : L.Interp) (x : QuantumComp L spec W A)
    (ρ : SubState A) (f : (Σ u, W u) → R.D → Bool) :
    jointLaw R I x ρ f {true} = ∑' p : Σ u, W u, ENNReal.ofReal
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ diagonal fun d ↦ if f p d then 1 else 0) *
        (R.jointPost I x ρ p).matrix).trace.re := by
  rw [jointLaw, Measure.sum_apply _ (measurableSet_singleton true)]
  refine tsum_congr fun p ↦ ?_
  rw [DSubInstrument.outcomeMeasure_map, Measure.sum_apply _ (measurableSet_singleton true),
    tsum_fintype]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton true),
    smul_eq_mul, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one,
    mul_zero]
  have key (d : R.D) : ((measureReg p.1 R.D).branch d (R.jointPost I x ρ p).matrix).trace =
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Matrix.single d d (1 : ℂ)) *
        (R.jointPost I x ρ p).matrix).trace := by
    rw [measureReg, DSubInstrument.branch_ofKraus_apply, MatrixMap.trace_conj_apply,
      one_kronecker_single_conjTranspose_mul_self]
  rw [← sum_ite_one_kronecker_single, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases hd : f p d
    · rw [ite_eq_left hd, ite_eq_left hd, key]
    · rw [ite_eq_right hd, ite_eq_right hd, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
        ENNReal.ofReal_zero]
  · intro d _
    by_cases hd : f p d
    · rw [ite_eq_left hd, ← key, ← DSubInstrument.matrix_post]
      exact SubState.trace_re_nonneg _
    · rw [ite_eq_right hd, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]

end jointLaw

/-! ## Recorded reads agree with the measured register -/

section fundamental

/-- `tr((1 ⊗ N) (1 ⊗ K) σ (1 ⊗ K)ᴴ) = tr((1 ⊗ Kᴴ N K) σ)`. -/
theorem trace_one_kronecker_mul_conj {B S S' : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    [Fintype S'] (N : Matrix S S ℂ) (K : Matrix S S' ℂ) (σ : Matrix (B × S') (B × S') ℂ) :
    (((1 : Matrix B B ℂ) ⊗ₖ N) * MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) σ).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ (Kᴴ * N * K)) * σ).trace := by
  rw [MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w}
  {A : QReg}

/-- **Recorded reads agree with the measured register, up to `ε`.** Let `M` intertwine a runtime
`R₁` (whose register holds classical tables) with `R₂`, and at every leaf `p` let the post-state
against `R₁` be supported on a projector `Pf (lg p)`. If `Q l` is a property of the basis states
of `R₂`'s register with `Pf Mᴴ Q M Pf = c • Pf` and `c ≥ 1 - ε` wherever the post-state is not
zero, then measuring `R₂`'s register at the end finds `Q (lg p)` except with probability `ε`:
every event `E` of the leaf has probability at most that of `E` and `Q` jointly, plus `ε`. -/
theorem evalDistMap_le_jointLaw_add (R₁ R₂ : QuantumRuntime spec) (M : Matrix R₂.D R₁.D ℂ)
    (hM : Mᴴ * M = 1)
    (hstep : ∀ i r, (R₂.step i).branch r ∘ₗ (MatrixMap.conj M).amplifyLeft (spec.In i) =
      (MatrixMap.conj M).amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hinit : MatrixMap.conj M R₁.init.matrix = R₂.init.matrix)
    (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A)
    {Λ : Type*} (lg : (Σ u, W u) → Λ) (Pf : Λ → Matrix R₁.D R₁.D ℂ)
    (hPf : ∀ l, (Pf l)ᴴ = Pf l) (hPf' : ∀ l, Pf l * Pf l = Pf l)
    (Q : Λ → R₂.D → Prop) [∀ l, DecidablePred (Q l)] (c : Λ → ℝ)
    (hsand : ∀ l, Pf l * Mᴴ * diagonal (fun d ↦ if Q l d then (1 : ℂ) else 0) * M * Pf l =
      (c l : ℂ) • Pf l)
    (hsupp : ∀ p, MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Pf (lg p))
      (R₁.jointPost I x ρ p).matrix = (R₁.jointPost I x ρ p).matrix)
    (ε : ℝ) (hc : ∀ p, (R₁.jointPost I x ρ p).matrix ≠ 0 → 1 - ε ≤ c (lg p))
    (E : (Σ u, W u) → Prop) [DecidablePred E] :
    R₂.evalDistMap I x ρ (fun p ↦ decide (E p)) {true} ≤
      jointLaw R₂ I x ρ (fun p d ↦ decide (E p ∧ Q (lg p) d)) {true} + ENNReal.ofReal ε := by
  have hτ (p : Σ u, W u) : (R₂.jointPost I x ρ p).matrix =
      MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ M) (R₁.jointPost I x ρ p).matrix := by
    rw [QuantumRuntime.matrix_jointPost_of_simulation I hstep hinit x ρ p,
      MatrixMap.amplifyLeft_conj]
  have hN (p : Σ u, W u) (N : Matrix R₂.D R₂.D ℂ) :
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ N) * (R₂.jointPost I x ρ p).matrix).trace =
        (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (Pf (lg p) * Mᴴ * N * M * Pf (lg p))) *
          (R₁.jointPost I x ρ p).matrix).trace := by
    rw [hτ, trace_one_kronecker_mul_conj]
    conv_lhs => rw [← hsupp p]
    rw [trace_one_kronecker_mul_conj, hPf]
    simp only [Matrix.mul_assoc]
  have htr (p : Σ u, W u) : (R₂.jointPost I x ρ p).matrix.trace =
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Pf (lg p)) * (R₁.jointPost I x ρ p).matrix).trace := by
    rw [← Matrix.one_mul (R₂.jointPost I x ρ p).matrix, ← one_kronecker_one, hN,
      Matrix.mul_one, Matrix.mul_assoc (Pf (lg p)) Mᴴ M, hM, Matrix.mul_one, hPf']
  have hQ (p : Σ u, W u) :
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ diagonal (fun d ↦ if Q (lg p) d then 1 else 0)) *
        (R₂.jointPost I x ρ p).matrix).trace =
        (c (lg p) : ℂ) * (R₂.jointPost I x ρ p).matrix.trace := by
    rw [hN, hsand, kronecker_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, htr]
  have hsum : ∑' p : Σ u, W u, ENNReal.ofReal (R₂.jointPost I x ρ p).matrix.trace.re ≤ 1 := by
    let : MeasurableSpace (Σ u, W u) := ⊤
    have h := measure_univ_le (R₂.evalDist I x ρ)
    rw [← QuantumRuntime.evalDistMap_id,
      QuantumRuntime.evalDistMap_apply _ _ _ _ _ MeasurableSet.univ] at h
    simpa using h
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
    jointLaw_apply_true]
  calc _ ≤ ∑' p : Σ u, W u, (ENNReal.ofReal
          (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ diagonal fun d ↦
            if decide (E p ∧ Q (lg p) d) then 1 else 0) *
            (R₂.jointPost I x ρ p).matrix).trace.re +
          ENNReal.ofReal ε * ENNReal.ofReal (R₂.jointPost I x ρ p).matrix.trace.re) := by
        refine ENNReal.tsum_le_tsum fun p ↦ ?_
        by_cases hE : E p
        · have hd : (diagonal fun d ↦ if decide (E p ∧ Q (lg p) d) then (1 : ℂ) else 0) =
              diagonal fun d ↦ if Q (lg p) d then 1 else 0 := by
            simp [hE]
          have ha := SubState.trace_re_nonneg (R₂.jointPost I x ρ p)
          rw [hd, hQ, Complex.re_ofReal_mul]
          simp only [hE, decide_true, Set.indicator_apply, Set.mem_singleton_iff, ↓reduceIte,
            Pi.one_apply, mul_one]
          rw [← ENNReal.ofReal_mul' ha]
          refine le_trans ?_ ENNReal.ofReal_add_le
          refine ENNReal.ofReal_le_ofReal ?_
          by_cases h0 : (R₁.jointPost I x ρ p).matrix = 0
          · rw [hτ, h0, map_zero, Matrix.trace_zero, Complex.zero_re]
            simp
          · nlinarith [hc p h0]
        · simp [hE]
    _ = _ + ENNReal.ofReal ε * ∑' p : Σ u, W u,
          ENNReal.ofReal (R₂.jointPost I x ρ p).matrix.trace.re := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        simpa using mul_le_mul' (le_refl (ENNReal.ofReal ε)) hsum

/-- **Reads after a program agree with the measured register.** Under the intertwining of
`evalDistMap_le_jointLaw_add`, if basis calls against `R₁` project onto the tables answering the
read value (`hrd`), `Q log` satisfies `Pf Mᴴ Q M Pf = c • Pf` for the projector `Pf` onto the tables
consistent with `log`, and `c log ≥ 1 - ε` for every transcript of the reads, then every event of
the leaf, result and log of `withReads x rd oa` has probability at most that of the event jointly
with `Q log` on the measured register of `R₂`, plus `ε`. -/
theorem evalDistMap_withReads_le {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    [∀ t, DecidableEq (ospec t)] {β : Type} {W : QReg → Type}
    (R₁ R₂ : QuantumRuntime spec) (M : Matrix R₂.D R₁.D ℂ) (hM : Mᴴ * M = 1)
    (hstep : ∀ i r, (R₂.step i).branch r ∘ₗ (MatrixMap.conj M).amplifyLeft (spec.In i) =
      (MatrixMap.conj M).amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hinit : MatrixMap.conj M R₁.init.matrix = R₂.init.matrix)
    (ans : R₁.D → (t : ι) → ospec t) (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (hrd : ∀ B t c, (R₁.run₂ .instruments (rd B t)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ readProjector ans t c))
    (Q : QueryLog ospec → R₂.D → Prop) [∀ l, DecidablePred (Q l)] (c : QueryLog ospec → ℝ)
    (hsand : ∀ log, logProjector ans log * Mᴴ * diagonal (fun d ↦ if Q log d then (1 : ℂ) else 0) *
      M * logProjector ans log = (c log : ℂ) • logProjector ans log)
    (x : QuantumComp LocalSig.instruments.{0} spec W A) (oa : (Σ u, W u) → OracleComp ospec β)
    (ρ : SubState A) (ε : ℝ) (hc : ∀ p r, IsTranscript (oa p) r → 1 - ε ≤ c r.2)
    (E : (Σ u, W u × β × QueryLog ospec) → Prop) [DecidablePred E] :
    R₂.evalDistMap .instruments (withReads x rd oa) ρ (fun q ↦ decide (E q)) {true} ≤
      jointLaw R₂ .instruments (withReads x rd oa) ρ (fun q d ↦ decide (E q ∧ Q q.2.2.2 d))
        {true} + ENNReal.ofReal ε := by
  classical
  have hsupp (q : Σ u, W u × β × QueryLog ospec) :
      (if IsTranscript (oa ⟨q.1, q.2.1⟩) q.2.2 then
        MatrixMap.conj ((1 : Matrix q.1 q.1 ℂ) ⊗ₖ logProjector ans q.2.2.2) else 0)
        (R₁.jointPost .instruments (withReads x rd oa) ρ q).matrix =
      (R₁.jointPost .instruments (withReads x rd oa) ρ q).matrix :=
    branch_run_withReads R₁ ans rd hrd x oa q _
  refine evalDistMap_le_jointLaw_add R₁ R₂ M hM hstep hinit .instruments (withReads x rd oa) ρ
    (fun q ↦ q.2.2.2) (logProjector ans) (conjTranspose_logProjector ans)
    (logProjector_mul_self ans) Q c hsand (fun q ↦ ?_) ε (fun q hq ↦ ?_) E
  · have h := hsupp q
    split_ifs at h
    · exact h
    · rw [← h, LinearMap.zero_apply, map_zero]
  · have h := hsupp q
    split_ifs at h with hT
    · exact hc _ _ hT
    · exact absurd h.symm (by rwa [LinearMap.zero_apply])

/-! ## Basis calls on a table oracle -/

/-- The block `⟨o|U|t, 0⟩` of a table oracle at the input `(t, 0)` and the output
`o = (t', c)`: the projection onto the tables answering `c` at `t` if `t' = t`, and zero
otherwise. -/
theorem submatrix_tableOracle {T X Y : Type} [Fintype T] [DecidableEq T] [DecidableEq X]
    [DecidableEq Y] [AddCommGroup Y] (read : T → X → Y) (t : X) (o : X × Y) :
    (tableOracle read).submatrix (fun d ↦ (o, d)) (fun d ↦ ((t, (0 : Y)), d)) =
      if o.1 = t then diagonal fun τ ↦ if read τ t = o.2 then 1 else 0 else 0 := by
  obtain ⟨t', c⟩ := o
  ext τ τ'
  by_cases ht : t' = t
  · subst ht
    by_cases hτ : τ = τ'
    · subst hτ
      by_cases hc : read τ t' = c <;> simp [tableOracle_apply, oracleEquiv_apply, hc, eq_comm]
    · simp [tableOracle_apply, oracleEquiv_apply, hτ]
  · simp [tableOracle_apply, oracleEquiv_apply, ht]

/-- **A basis read of a table oracle** at `(t, 0)` reporting the answer register: summing the
blocks over the outputs with answer `c` gives the projection onto the tables answering `c`. -/
theorem sum_conj_submatrix_tableOracle {T X Y : Type} [Fintype T] [DecidableEq T] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] (B : Type) [Fintype B]
    [DecidableEq B] (read : T → X → Y) (t : X) (c : Y) :
    (∑ o : X × Y, if o.2 = c then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (tableOracle read).submatrix (fun d ↦ (o, d)) (fun d ↦ ((t, (0 : Y)), d))) else 0) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun τ ↦ if read τ t = c then 1 else 0) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single c]
    · rw [ite_eq_left rfl, submatrix_tableOracle, ite_eq_left rfl]
    · intro c' _ hc'
      rw [ite_eq_right hc']
    · simp
  · intro t' _ ht'
    refine Finset.sum_eq_zero fun c' _ ↦ ?_
    rw [submatrix_tableOracle, ite_eq_right ht', kronecker_zero, MatrixMap.conj_zero]
    simp
  · simp

end fundamental

end Quantum.Sponge

end
