module

public import Quantum.Sponge.Simulate
public import Quantum.Sponge.Reads.Log
public import Quantum.Sponge.Oracle
public import Quantum.Sponge.Keccak

@[expose] public section

/-!
# Collision and preimage resistance of the sponge in the QRPM

The end-to-end bounds of Corollaries 6.13 and 6.14 of Alagic, Carolan, Majenz and Tokat
(ePrint 2025/731), with explicit constants. A program `x` in the quantum random-permutation model
on `X × Z` makes at most `q` calls; at its leaf it names two nonempty messages of at most `l`
blocks (`qrpm_sponge_collision_le`), or one (`qrpm_sponge_preimage_le`). The `_permBadFrac`
versions keep the fraction of permutations that are not `PermGood π G`, for any `G`; at
Keccak-256 sizes they give `keccak256_qrpm_collision_le` and `keccak256_qrpm_preimage_le`.

1. Given `π`, `x` is simulated by the three random functions (`qrpmEvalDistMap_eq_simulate`).
2. The sponge is evaluated classically after the simulation, through reads of `h`, `k` and `k'`
   (`pairReads`); against fixed functions the reads return the hash and log `spongeReads`
   (`spongeEvalDistMap_withReads`, `logRun_spongeEvalM`).
3. The reads are recorded in the measured databases (`spongeEvalDistMap_withReads_le_heldBy`); a
   transcript held by the databases is a collision (preimage) in them
   (`collisionBad_of_isTranscript`), whose weight `eventWeight_spongeCompressedRuntime_le` bounds
   (`spongeEvalDistMap_le_of_reads`).
4. Averaging over `π` costs the fraction of bad permutations (`average_le`, `permBadFrac_le`).
-/

open Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ENNReal

universe u u₁ v₁

namespace Quantum.Sponge

open Quantum

/-! ## Answering a classical algorithm with fixed answers -/

section logRun

variable {ι : Type} {ospec : OracleSpec.{0, 0} ι} {β γ : Type}

/-- Run `oa`, answering each query `t` with `ans t`, and return the result with the log of the
queries and answers. -/
def logRun (ans : (t : ι) → ospec t) : OracleComp ospec β → β × QueryLog ospec :=
  OracleComp.construct (C := fun _ ↦ β × QueryLog ospec)
    (fun b ↦ (b, []))
    (fun t _ ih ↦ ((ih (ans t)).1, ⟨t, ans t⟩ :: (ih (ans t)).2))

variable (ans : (t : ι) → ospec t)

theorem logRun_pure (b : β) : logRun ans (pure b : OracleComp ospec β) = (b, []) :=
  rfl

theorem logRun_query_bind (t : ι) (k : ospec t → OracleComp ospec β) :
    logRun ans (liftM (ospec.query t) >>= k) =
      ((logRun ans (k (ans t))).1, ⟨t, ans t⟩ :: (logRun ans (k (ans t))).2) :=
  rfl

theorem logRun_query (t : ι) :
    logRun ans (liftM (ospec.query t) : OracleComp ospec (ospec t)) = (ans t, [⟨t, ans t⟩]) :=
  rfl

theorem logRun_bind (oa : OracleComp ospec β) (g : β → OracleComp ospec γ) :
    logRun ans (oa >>= g) =
      ((logRun ans (g (logRun ans oa).1)).1,
        (logRun ans oa).2 ++ (logRun ans (g (logRun ans oa).1)).2) := by
  induction oa using OracleComp.inductionOn with
  | pure b => rw [pure_bind]; rfl
  | query_bind t k ih =>
    rw [bind_assoc, logRun_query_bind, logRun_query_bind, ih]
    rfl

theorem logRun_map (oa : OracleComp ospec β) (f : β → γ) :
    logRun ans (f <$> oa) = (f (logRun ans oa).1, (logRun ans oa).2) := by
  rw [map_eq_bind_pure_comp, logRun_bind]
  simp [logRun_pure]

/-- The run with fixed answers is a transcript. -/
theorem isTranscript_logRun (oa : OracleComp ospec β) : IsTranscript oa (logRun ans oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => exact (isTranscript_pure b _).mpr rfl
  | query_bind t k ih => exact (isTranscript_query_bind t k _).mpr ⟨ans t, _, rfl, ih (ans t)⟩

/-- The log of the run with fixed answers holds these answers. -/
theorem logRun_consistent (oa : OracleComp ospec β) :
    ∀ e ∈ (logRun ans oa).2, ans e.1 = e.2 := by
  induction oa using OracleComp.inductionOn with
  | pure b => simp [logRun_pure]
  | query_bind t k ih =>
    intro e he
    rw [logRun_query_bind, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

/-- A transcript whose answers are those of `ans` is the run with the answers `ans`. -/
theorem eq_logRun_of_isTranscript {oa : OracleComp ospec β} {r : β × QueryLog ospec}
    (hr : IsTranscript oa r) (hc : ∀ e ∈ r.2, ans e.1 = e.2) : r = logRun ans oa := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure b => exact (isTranscript_pure b r).mp hr
  | query_bind t k ih =>
    obtain ⟨c, log, hlog, hk⟩ := (isTranscript_query_bind t k r).mp hr
    have hc0 : ans t = c := hc ⟨t, c⟩ (by simp [hlog])
    subst hc0
    have := ih (ans t) hk fun e he ↦ hc e (by simp [hlog, he])
    rw [logRun_query_bind, ← this]
    exact Prod.ext rfl hlog

theorem isTranscript_and_iff (oa : OracleComp ospec β) (r : β × QueryLog ospec) :
    (IsTranscript oa r ∧ ∀ e ∈ r.2, ans e.1 = e.2) ↔ r = logRun ans oa :=
  ⟨fun h ↦ eq_logRun_of_isTranscript ans h.1 h.2,
    by rintro rfl; exact ⟨isTranscript_logRun ans oa, logRun_consistent ans oa⟩⟩

end logRun

/-! ## The reads after a program, against a runtime that answers them deterministically -/

section branch

variable {ι : Type} {ospec : OracleSpec.{0, 0} ι} {β : Type} {spec : QuantumOracleSpec.{u₁, v₁}}
  (R : QuantumRuntime spec) {W : QReg → Type} {A : QReg}

/-- The branch of `withReads x rd oa` at a leaf: the branch of the logged reads after the branch of
`x`. -/
theorem branch_run_withReads_mk (x : QuantumComp LocalSig.instruments.{0} spec W A)
    (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (oa : (Σ u, W u) → OracleComp ospec β) (u : QReg) (w : W u) (r : β × QueryLog ospec) :
    (R.run .instruments (withReads x rd oa)).branch ⟨u, (w, r)⟩ =
      (R.run₂ .instruments (loggedReads (rd u) (oa ⟨u, w⟩))).branch r ∘ₗ
        (R.run .instruments x).branch ⟨u, w⟩ := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [withReads, QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply, LinearMap.comp_apply,
    tsum_eq_single ⟨u, w⟩ fun p hp ↦ ?_]
  · rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply,
      tsum_eq_single (⟨u, ⟨rfl, r⟩⟩ : Σ v, QuantumComp₂.Leaf u (β × QueryLog ospec) v)
        fun l hl ↦ ?_]
    · rw [QuantumRuntime.run_pure]
      dsimp only
      rw [cast_eq, DSubInstrument.branch_ret_self, LinearMap.id_apply]
      rfl
    · obtain ⟨v, hv, r'⟩ := l
      obtain rfl : v = u := hv
      rw [QuantumRuntime.run_pure]
      dsimp only
      rw [cast_eq, DSubInstrument.branch_ret_of_ne, LinearMap.zero_apply]
      intro h
      have := (Prod.ext_iff.mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).2
      subst this
      exact hl rfl
  · obtain ⟨u', w'⟩ := p
    rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
    refine (tsum_congr fun l ↦ ?_).trans tsum_zero
    obtain ⟨v, hv, r'⟩ := l
    obtain rfl : v = u' := hv
    rw [QuantumRuntime.run_pure]
    dsimp only
    rw [cast_eq, DSubInstrument.branch_ret_of_ne, LinearMap.zero_apply]
    intro h
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
    have := (Prod.ext_iff.mp (eq_of_heq hh)).1
    subst this
    exact hp rfl

/-- If the logged reads after the leaf `p` deterministically report `d p`, observing `withReads`
is observing `x` together with `d`. -/
theorem evalDistMap_withReads_of_branch {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp LocalSig.instruments.{0} spec W A)
    (rd : (B : QReg) → QueryImpl ospec (QComp spec B B))
    (oa : (Σ u, W u) → OracleComp ospec β) (d : (Σ u, W u) → β × QueryLog ospec)
    (hd : ∀ u w, (R.run₂ .instruments (loggedReads (rd u) (oa ⟨u, w⟩))).branch (d ⟨u, w⟩) =
      LinearMap.id)
    (hd₀ : ∀ u w r, r ≠ d ⟨u, w⟩ →
      (R.run₂ .instruments (loggedReads (rd u) (oa ⟨u, w⟩))).branch r = 0)
    (ρ : SubState A) (g : (Σ u, W u × β × QueryLog ospec) → γ) :
    R.evalDistMap .instruments (withReads x rd oa) ρ g =
      R.evalDistMap .instruments x ρ fun p ↦ g ⟨p.1, p.2, d p⟩ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs,
    ENNReal.tsum_sigma', ENNReal.tsum_sigma']
  refine tsum_congr fun u ↦ ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun w ↦ ?_
  rw [tsum_eq_single (d ⟨u, w⟩) fun r hr ↦ ?_]
  · simp [branch_run_withReads_mk, hd]
  · simp [branch_run_withReads_mk, hd₀ u w r hr]

end branch

/-! ## The oracles of fixed functions answer the reads -/

section fixed

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- The oracles of fixed functions `t = (h, k, k')` as an emulated oracle on a trivial private
register. -/
@[reducible]
noncomputable def fnOracle (t : (Z → X) × (X → Z) × (X → Z)) :
    EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of Unit
  init := SubState.basis ()
  U
    | .h => basisMatrix (Prod.map (oracleEquiv t.1) (id : Unit → Unit))
    | .k => basisMatrix (Prod.map (oracleEquiv t.2.1) (id : Unit → Unit))
    | .k' => basisMatrix (Prod.map (oracleEquiv t.2.2) (id : Unit → Unit))
  unitary
    | .h => mem_unitaryGroup_iff'.mpr (conjTranspose_basisMatrix_mul_self
        ((oracleEquiv t.1).injective.prodMap Function.injective_id))
    | .k => mem_unitaryGroup_iff'.mpr (conjTranspose_basisMatrix_mul_self
        ((oracleEquiv t.2.1).injective.prodMap Function.injective_id))
    | .k' => mem_unitaryGroup_iff'.mpr (conjTranspose_basisMatrix_mul_self
        ((oracleEquiv t.2.2).injective.prodMap Function.injective_id))

/-- The runtime of `fnOracle t`, for programs over `spongeSpec X Z`. -/
@[reducible]
noncomputable def fnRuntime (t : (Z → X) × (X → Z) × (X → Z)) : QuantumRuntime (spongeSpec X Z) :=
  (fnOracle t).toRuntime

theorem spongeFnRuntime_eq_fnRuntime (t : (Z → X) × (X → Z) × (X → Z)) :
    spongeFnRuntime t.1 t.2.1 t.2.2 = fnRuntime t := by
  refine congrArg (QuantumRuntime.mk (QReg.of Unit) (SubState.basis ())) (funext fun i ↦ ?_)
  cases i <;> exact DSubInstrument.ext (funext fun _ ↦ branch_frame_oracleQuery _ Unit)

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
/-- Kraus maps of a `0`/`1` multiple of the identity. -/
theorem conj_one_kronecker_diagonal_ite {B T : Type} [Fintype B] [DecidableEq B] [Fintype T]
    [DecidableEq T] (P : Prop) [Decidable P] :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun _ : T ↦ if P then (1 : ℂ) else 0) =
      if P then LinearMap.id else 0 := by
  by_cases hP : P
  · simp only [hP, ite_true, diagonal_one, one_kronecker_one, MatrixMap.conj_one]
  · simp only [hP, ite_false, diagonal_zero, kronecker_zero, MatrixMap.conj_zero]

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
/-- The sum of the branches of a basis call whose blocks select one output `o0`. -/
theorem sum_ite_conj_block {B T M Y : Type} [Fintype B] [DecidableEq B] [Fintype T]
    [DecidableEq T] [Fintype M] [DecidableEq M] [DecidableEq Y] (read : M → Y) (o0 : M) (c : Y)
    (blk : M → Matrix T T ℂ) (hblk : ∀ o, blk o = if o = o0 then 1 else 0) :
    (∑ o, if read o = c then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ blk o) else 0) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun _ : T ↦ if read o0 = c then 1 else 0) := by
  rw [Finset.sum_eq_single o0 (fun o _ ho ↦ by simp [hblk, ho, MatrixMap.conj_zero])
    (fun h ↦ absurd (Finset.mem_univ o0) h), conj_one_kronecker_diagonal_ite]
  by_cases hc : read o0 = c <;> simp [hc, hblk, MatrixMap.conj_one]

/-- Against fixed functions, a classical read reporting `c` is the identity when `c` is the
answer, and zero otherwise. -/
theorem branch_run₂_spongeReadImpl_fn (t : (Z → X) × (X → Z) × (X → Z)) (B : QReg)
    (q : SpongeQuery X Z) (c : spongeOSpec X Z q) :
    ((fnRuntime t).run₂ .instruments (spongeReadImpl X Z B q)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        readProjector (fun _ : (fnRuntime t).D ↦ spongeAns t) q c) := by
  cases q with
  | h z =>
    change ((fnOracle t).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .h B (z, (0 : X))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    refine (sum_ite_conj_block (fun o : Z × X ↦ o.2) (z, t.1 z) c _ fun o ↦ ?_).trans rfl
    ext d d'
    obtain rfl : d = d' := Subsingleton.elim _ _
    by_cases ho : o = (z, t.1 z) <;> simp [ho, EmulatedOracle.block_apply, oracleEquiv_apply]
  | k x =>
    change ((fnOracle t).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    refine (sum_ite_conj_block (fun o : X × Z ↦ o.2) (x, t.2.1 x) c _ fun o ↦ ?_).trans rfl
    ext d d'
    obtain rfl : d = d' := Subsingleton.elim _ _
    by_cases ho : o = (x, t.2.1 x) <;> simp [ho, EmulatedOracle.block_apply, oracleEquiv_apply]
  | k' x =>
    change ((fnOracle t).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k' B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    refine (sum_ite_conj_block (fun o : X × Z ↦ o.2) (x, t.2.2 x) c _ fun o ↦ ?_).trans rfl
    ext d d'
    obtain rfl : d = d' := Subsingleton.elim _ _
    by_cases ho : o = (x, t.2.2 x) <;> simp [ho, EmulatedOracle.block_apply, oracleEquiv_apply]

/-- Against fixed functions, the logged reads of `oa` report their run with the functions'
answers. -/
theorem branch_run₂_loggedReads_fn_self {β : Type} (t : (Z → X) × (X → Z) × (X → Z))
    (B : QReg) (oa : OracleComp (spongeOSpec X Z) β) :
    ((fnRuntime t).run₂ .instruments (loggedReads (spongeReadImpl X Z B) oa)).branch
      (logRun (spongeAns t) oa) = LinearMap.id := by
  rw [branch_run₂_loggedReads (fnRuntime t) (fun _ ↦ spongeAns t) (spongeReadImpl X Z)
    (branch_run₂_spongeReadImpl_fn t) B oa _, ite_eq_left (isTranscript_logRun _ oa),
    logProjector, conj_one_kronecker_diagonal_ite, ite_eq_left (logRun_consistent _ oa)]

/-- Against fixed functions, the logged reads of `oa` report nothing but their run with the
functions' answers. -/
theorem branch_run₂_loggedReads_fn_of_ne {β : Type} (t : (Z → X) × (X → Z) × (X → Z))
    (B : QReg) (oa : OracleComp (spongeOSpec X Z) β) {r : β × QueryLog (spongeOSpec X Z)}
    (hr : r ≠ logRun (spongeAns t) oa) :
    ((fnRuntime t).run₂ .instruments (loggedReads (spongeReadImpl X Z B) oa)).branch r = 0 := by
  rw [branch_run₂_loggedReads (fnRuntime t) (fun _ ↦ spongeAns t) (spongeReadImpl X Z)
    (branch_run₂_spongeReadImpl_fn t) B oa r]
  by_cases h₁ : IsTranscript oa r
  · rw [ite_eq_left h₁, logProjector, conj_one_kronecker_diagonal_ite,
      ite_eq_right fun h₂ ↦ hr ((isTranscript_and_iff _ oa r).mp ⟨h₁, h₂⟩)]
  · rw [ite_eq_right h₁]

/-- **Reads of fixed functions.** With uniform `(h, k, k')`, observing the program followed by
classical reads is observing the program together with the run of the reads answered by the
functions. -/
theorem spongeEvalDistMap_withReads {W : QReg → Type} {A : QReg} {β : Type} {γ : Type*}
    [MeasurableSpace γ] (x : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A)
    (oa : (Σ u, W u) → OracleComp (spongeOSpec X Z) β) (ρ : SubState A)
    (g : (Σ u, W u × β × QueryLog (spongeOSpec X Z)) → γ) :
    spongeEvalDistMap .instruments (withReads x (spongeReadImpl X Z) oa) ρ (fun _ ↦ g) =
      spongeEvalDistMap .instruments x ρ fun t p ↦ g ⟨p.1, p.2, logRun (spongeAns t) (oa p)⟩ := by
  rw [spongeEvalDistMap_eq_sum, spongeEvalDistMap_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [spongeFnRuntime_eq_fnRuntime]
  exact evalDistMap_withReads_of_branch (fnRuntime t) x _ oa _
    (fun u _ ↦ branch_run₂_loggedReads_fn_self t u _)
    (fun u _ _ hr ↦ branch_run₂_loggedReads_fn_of_ne t u _ hr) ρ g

end fixed

/-! ## The joint law of a database event is its weight -/

section joint

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, u₁}} {W : QReg → Type} {A : QReg}

/-- The joint law of an event grows with the event. -/
theorem jointLaw_true_mono (R : QuantumRuntime spec) {L : LocalSig} (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) {f g : (Σ u, W u) → R.D → Bool}
    (h : ∀ p d, f p d = true → g p d = true) :
    jointLaw R I x ρ f {true} ≤ jointLaw R I x ρ g {true} := by
  simp only [jointLaw, Measure.sum_apply _ (measurableSet_singleton true),
    DSubInstrument.outcomeMeasure_map, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton true), smul_eq_mul]
  refine ENNReal.tsum_le_tsum fun p ↦ ENNReal.tsum_le_tsum fun d ↦ ?_
  gcongr
  by_cases hf : f p d = true
  · simp [hf, h p d hf]
  · simp [Bool.eq_false_iff.mpr hf]

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- The joint law of "the measured databases lie in `S`" is the weight of `dbsProjector S`. -/
theorem jointLaw_dbs_eq_eventWeight (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] {L : LocalSig}
    (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) :
    jointLaw (spongeCompressedRuntime X Z) I x ρ (fun _ D ↦ decide (D.toDbs ∈ S)) {true} =
      (spongeCompressedRuntime X Z).eventWeight I (dbsProjector S) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime X Z).init.matrix) := by
  rw [jointLaw_apply_true, QuantumRuntime.eventWeight]
  refine tsum_congr fun p ↦ ?_
  have hq := isStarProjection_labelProjector (α := ℂ) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S))
    true
  have hs : (dbsProjector S)ᴴ = dbsProjector S := hq.isSelfAdjoint.star_eq
  have hi : dbsProjector S * dbsProjector S = dbsProjector S := hq.isIdempotentElem.eq
  have hK : ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ dbsProjector S)ᴴ * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ
      dbsProjector S) = (1 : Matrix p.1 p.1 ℂ) ⊗ₖ dbsProjector S := by
    rw [conjTranspose_kronecker, conjTranspose_one, hs, ← mul_kronecker_mul, Matrix.one_mul, hi]
  rw [MatrixMap.trace_conj_apply, hK]
  rfl

end joint

/-! ## Budgets -/

/-- A per-port budget gives the total budget of its sum. -/
theorem QuantumComp.isTotalQueryBound_of_isQueryBound {L : LocalSig.{u, u₁}}
    {s : QuantumOracleSpec.{u₁, v₁}} [Fintype s.Port] [DecidableEq s.Port] {W : QReg → Type}
    {A : QReg} {x : QuantumComp L s W A} {b : s.Port → ℕ} (hx : x.IsQueryBound b) :
    x.IsTotalQueryBound (∑ i, b i) := by
  induction x using QuantumComp.inductionOn generalizing b with
  | pure _ _ => exact QuantumComp.isTotalQueryBound_pure _ _
  | primBind _ o k ih =>
    rw [QuantumComp.isTotalQueryBound_primBind_iff]
    exact fun r ↦ ih r fun i ↦ (QuantumComp.isQueryBoundAt_primBind_iff o k i _).mp (hx i) r
  | queryBind _ j E ℓ k ih =>
    rw [QuantumComp.isTotalQueryBound_queryBind_iff]
    have hj := ((QuantumComp.isQueryBoundAt_queryBind_iff j E ℓ k j (b j)).mp (hx j)).1 rfl
    have hsum : ∑ i, b i = b j + ∑ i ∈ Finset.univ.erase j, b i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    refine ⟨by omega, fun r ↦ ?_⟩
    have hb : (k r).IsQueryBound (Function.update b j (b j - 1)) := by
      intro i
      by_cases hi : j = i
      · subst hi
        rw [Function.update_self]
        exact hj.2 r
      · rw [Function.update_of_ne (Ne.symm hi)]
        exact ((QuantumComp.isQueryBoundAt_queryBind_iff j E ℓ k i (b i)).mp (hx i)).2 hi r
    refine (ih r hb).mono (le_of_eq ?_)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self,
      Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
    omega

section reads

variable {X Z : Type} [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z))

/-- A classical read of `h`. -/
def readHQ (z : Z) : OracleComp (spongeOSpec X Z) X :=
  liftM ((spongeOSpec X Z).query (.h z))

/-- A classical read of `k`. -/
def readKQ (x : X) : OracleComp (spongeOSpec X Z) Z :=
  liftM ((spongeOSpec X Z).query (.k x))

/-- A classical read of `k'`. -/
def readK'Q (x : X) : OracleComp (spongeOSpec X Z) Z :=
  liftM ((spongeOSpec X Z).query (.k' x))

/-- The sponge's evaluation of two messages through classical reads. -/
def pairReads (mm : List X × List X) : OracleComp (spongeOSpec X Z) (X × X) := do
  let a ← spongeEvalM π readHQ readKQ readK'Q mm.1
  let b ← spongeEvalM π readHQ readKQ readK'Q mm.2
  pure (a, b)

theorem isQueryBoundP_evalRoundM (s : X × Z) (b : X) (i : SpongePort) :
    IsQueryBoundP (evalRoundM π readHQ readKQ readK'Q s b) (fun q ↦ q.port = i) 1 := by
  cases i <;> simp [evalRoundM, readHQ, readKQ, readK'Q, SpongeQuery.port]

theorem isQueryBoundP_spongeEvalM (m : List X) (i : SpongePort) :
    IsQueryBoundP (spongeEvalM π readHQ readKQ readK'Q m) (fun q ↦ q.port = i) m.length := by
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  suffices h : ∀ s, IsQueryBoundP (m.foldlM (evalRoundM π readHQ readKQ readK'Q) s)
      (fun q ↦ q.port = i) m.length from h _
  induction m with
  | nil => exact fun s ↦ isQueryBoundP_pure _ _ _
  | cons b m ih =>
    intro s
    rw [List.foldlM_cons]
    exact (isQueryBoundP_bind (isQueryBoundP_evalRoundM π s b i) fun s' _ ↦ ih s').mono
      (by simp [Nat.add_comm])

theorem isQueryBoundP_pairReads (mm : List X × List X) (i : SpongePort) :
    IsQueryBoundP (pairReads π mm) (fun q ↦ q.port = i) (mm.1.length + mm.2.length) :=
  (isQueryBoundP_bind (isQueryBoundP_spongeEvalM π mm.1 i) fun _ _ ↦
    isQueryBoundP_bind (isQueryBoundP_spongeEvalM π mm.2 i) fun _ _ ↦
      isQueryBoundP_pure _ _ 0).mono (by simp)

variable (t : (Z → X) × (X → Z) × (X → Z))

theorem logRun_evalRoundM (s : X × Z) (b : X) :
    (logRun (spongeAns t) (evalRoundM π readHQ readKQ readK'Q s b)).1 =
        absorbStep (spongePerm t π) s b ∧
      (logRun (spongeAns t) (evalRoundM π readHQ readKQ readK'Q s b)).2.map toSpongeRead =
        roundReads π t.1 t.2.1 t.2.2 s b := by
  simp only [evalRoundM, readHQ, readKQ, readK'Q, logRun_bind, logRun_query, logRun_pure]
  exact ⟨rfl, rfl⟩

theorem logRun_foldlM (m : List X) (s : X × Z) (L : List (SpongeRead X Z)) :
    (logRun (spongeAns t) (m.foldlM (evalRoundM π readHQ readKQ readK'Q) s)).1 =
        (m.foldl (logStep π t.1 t.2.1 t.2.2) (s, L)).1 ∧
      L ++ (logRun (spongeAns t) (m.foldlM (evalRoundM π readHQ readKQ readK'Q) s)).2.map
        toSpongeRead = (m.foldl (logStep π t.1 t.2.1 t.2.2) (s, L)).2 := by
  induction m generalizing s L with
  | nil => simp [logRun_pure]
  | cons b m ih =>
    obtain ⟨e₁, e₂⟩ := logRun_evalRoundM π t s b
    obtain ⟨i₁, i₂⟩ := ih (absorbStep (spongePerm t π) s b) (L ++ roundReads π t.1 t.2.1 t.2.2 s b)
    have hstep : logStep π t.1 t.2.1 t.2.2 (s, L) b =
        (absorbStep (spongePerm t π) s b, L ++ roundReads π t.1 t.2.1 t.2.2 s b) := rfl
    rw [List.foldlM_cons, logRun_bind, List.foldl_cons, hstep, e₁]
    refine ⟨i₁, ?_⟩
    rw [List.map_append, e₂, ← i₂, List.append_assoc]

/-- Answered by `t`, the sponge's evaluation through reads returns the hash under
`φ = spongePerm t π` and logs `spongeReads`. -/
theorem logRun_spongeEvalM (m : List X) :
    (logRun (spongeAns t) (spongeEvalM π readHQ readKQ readK'Q m)).1 =
        spongeHash (spongePerm t π) m ∧
      (logRun (spongeAns t) (spongeEvalM π readHQ readKQ readK'Q m)).2.map toSpongeRead =
        spongeReads π t.1 t.2.1 t.2.2 m := by
  obtain ⟨h₁, h₂⟩ := logRun_foldlM π t m (0, 0) []
  rw [spongeEvalM, logRun_map]
  refine ⟨?_, ?_⟩
  · rw [h₁, fst_foldl_logStep]
    rfl
  · exact (List.nil_append _).symm.trans h₂

theorem logRun_pairReads (mm : List X × List X) :
    (logRun (spongeAns t) (pairReads π mm)).1 =
        (spongeHash (spongePerm t π) mm.1, spongeHash (spongePerm t π) mm.2) ∧
      (logRun (spongeAns t) (pairReads π mm)).2.map toSpongeRead =
        spongeReads π t.1 t.2.1 t.2.2 mm.1 ++ spongeReads π t.1 t.2.1 t.2.2 mm.2 := by
  obtain ⟨a₁, a₂⟩ := logRun_spongeEvalM π t mm.1
  obtain ⟨b₁, b₂⟩ := logRun_spongeEvalM π t mm.2
  refine ⟨?_, ?_⟩ <;> simp [pairReads, logRun_bind, logRun_map, a₁, b₁, ← a₂, ← b₂]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The databases holding every read of a log give functions consistent with it. -/
theorem fill_consistent [Zero X] [Zero Z] {D : Dbs X Z} {log : QueryLog (spongeOSpec X Z)}
    (hD : ∀ e ∈ log.map toSpongeRead, e.HeldBy D) : ∀ e ∈ log, spongeAns D.fill e.1 = e.2 := by
  rintro ⟨q, a⟩ he
  have := hD _ (List.mem_map.mpr ⟨_, he, rfl⟩)
  cases q with
  | h z => exact Dbs.fill_h this
  | k x => exact Dbs.fill_k this
  | k' x => exact Dbs.fill_k' this

variable {Y : Type} {out : X → Y}

/-- A transcript of the reads of two distinct nonempty messages with equal outputs, all of whose
reads the databases hold, is a collision in the databases. -/
theorem collisionBad_of_isTranscript {mm : List X × List X} (hm : mm.1 ≠ []) (hm' : mm.2 ≠ [])
    (hne : mm.1 ≠ mm.2) {r : (X × X) × QueryLog (spongeOSpec X Z)}
    (hr : IsTranscript (pairReads π mm) r) (hout : out r.1.1 = out r.1.2) {D : Dbs X Z}
    (hD : ∀ e ∈ r.2.map toSpongeRead, e.HeldBy D) : D ∈ CollisionBad π out := by
  have hrun := eq_logRun_of_isTranscript (spongeAns D.fill) hr (fill_consistent hD)
  obtain ⟨h₁, h₂⟩ := logRun_pairReads π D.fill mm
  rw [← hrun] at h₁ h₂
  rw [h₂] at hD
  rw [h₁] at hout
  exact collision_of_heldBy π D.fill.1 D.fill.2.1 D.fill.2.2 hm hm' hne
    (fun e he ↦ hD e (List.mem_append_left _ he)) (fun e he ↦ hD e (List.mem_append_right _ he))
    hout

/-- A transcript of the reads of a nonempty message with output `y0`, all of whose reads the
databases hold, is a path to `y0` in the databases. -/
theorem preimageBad_of_isTranscript {m : List X} (hm : m ≠ []) {y0 : Y}
    {r : X × QueryLog (spongeOSpec X Z)}
    (hr : IsTranscript (spongeEvalM π readHQ readKQ readK'Q m) r) (hout : out r.1 = y0)
    {D : Dbs X Z} (hD : ∀ e ∈ r.2.map toSpongeRead, e.HeldBy D) : D ∈ PreimageBad π out y0 := by
  have hrun := eq_logRun_of_isTranscript (spongeAns D.fill) hr (fill_consistent hD)
  obtain ⟨h₁, h₂⟩ := logRun_spongeEvalM π D.fill m
  rw [← hrun] at h₁ h₂
  rw [h₂] at hD
  rw [h₁] at hout
  exact reachesOutput_of_heldBy π D.fill.1 D.fill.2.1 D.fill.2.2 hm hD hout

end reads

/-! ## The bound for a fixed permutation -/

section fixedPerm

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- Observations of programs over the three functions are subprobabilities. -/
theorem spongeEvalDistMap_apply_le_one {L : LocalSig} {W : QReg → Type*} {A : QReg} {β : Type*}
    [MeasurableSpace β] (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Z → X) × (X → Z) × (X → Z) → (Σ u, W u) → β) (s : Set β) :
    spongeEvalDistMap I x ρ f s ≤ 1 := by
  let : MeasurableSpace (Σ u, W u) := ⊤
  have h (t : (Z → X) × (X → Z) × (X → Z)) :
      (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ (f t) s ≤ 1 :=
    calc _ ≤ (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ (f t) Set.univ :=
          measure_mono (Set.subset_univ s)
      _ = (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ (fun p ↦ p) Set.univ := by
          rw [QuantumRuntime.evalDistMap_apply_univ, QuantumRuntime.evalDistMap_apply_univ]
      _ ≤ 1 := DSubInstrument.outcomeMeasure_apply_univ_le_one _ _
  rw [spongeEvalDistMap_eq_sum, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply]
  calc _ ≤ (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ *
        ∑ _t : (Z → X) × (X → Z) × (X → Z), (1 : ℝ≥0∞) := by
        gcongr with t
        exact h t
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)]

/-- **The bound for one permutation.** A program `y` over the three random functions, within the
budget `b` on each port, followed by classical reads `oa` making at most `lr` reads of each port:
an observation `P t p` that is the event `E` of the leaf, the reads' result and log, when the
reads are answered by `t`, has probability at most `6 T² ε + 2 (lr / |X| + 2 lr / |Z|)`, where
`T ≥ 3 (b + lr)`, if `E` with every read held by the databases puts them in `S`, an upward-closed
set without the empty databases into which fresh cells enter with probability at most `ε`. -/
theorem spongeEvalDistMap_le_of_reads {W : QReg → Type} {A : QReg} {β : Type}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A) {b : ℕ}
    (hy : y.IsQueryBound fun _ ↦ b) (oa : (Σ u, W u) → OracleComp (spongeOSpec X Z) β) {lr : ℕ}
    (hoa : ∀ p i, IsQueryBoundP (oa p) (fun q ↦ q.port = i) lr) (ρ : SubState A)
    (P : (Z → X) × (X → Z) × (X → Z) → (Σ u, W u) → Bool)
    (E : (Σ u, W u × β × QueryLog (spongeOSpec X Z)) → Prop)
    (hPE : ∀ t p, P t p = true ↔ E ⟨p.1, p.2, logRun (spongeAns t) (oa p)⟩)
    (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] (hup : UpClosed S) (hempty : emptyDbs ∉ S)
    (hES : ∀ q (D : Dbs X Z), E q → (∀ e ∈ q.2.2.2.map toSpongeRead, e.HeldBy D) → D ∈ S)
    {T : ℕ} (hT : 3 * (b + lr) ≤ T) {ε : ℝ≥0∞} (hε : FreshBound S T ε) :
    spongeEvalDistMap .instruments y ρ P {true} ≤
      6 * (T : ℝ≥0∞) ^ 2 * ε +
        ENNReal.ofReal (2 * (lr / Fintype.card X + (lr + lr) / Fintype.card Z)) := by
  classical
  have hP : spongeEvalDistMap .instruments y ρ P =
      spongeEvalDistMap .instruments (withReads y (spongeReadImpl X Z) oa) ρ
        (fun _ q ↦ decide (E q)) := by
    rw [spongeEvalDistMap_withReads]
    congr 1
    funext t p
    rw [Bool.eq_iff_iff, hPE, decide_eq_true_iff]
  have hcard : Fintype.card SpongePort = 3 := rfl
  have htot : (withReads y (spongeReadImpl X Z) oa).IsTotalQueryBound T := by
    refine (QuantumComp.isTotalQueryBound_of_isQueryBound
      (isQueryBound_withReads_spongeReadImpl hy oa (fun _ ↦ lr) hoa)).mono ?_
    calc ∑ i : SpongePort, ((fun _ ↦ b) + (fun _ ↦ lr) : SpongePort → ℕ) i =
        ∑ _i : SpongePort, (b + lr) := rfl
      _ = 3 * (b + lr) := by rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
      _ ≤ T := hT
  rw [hP]
  refine (spongeEvalDistMap_withReads_le_heldBy y oa (fun p ↦ hoa p .h) (fun p ↦ hoa p .k)
    (fun p ↦ hoa p .k') ρ E).trans ?_
  gcongr
  calc _ ≤ jointLaw (spongeCompressedRuntime X Z) .instruments
        (withReads y (spongeReadImpl X Z) oa) ρ (fun _ D ↦ decide (D.toDbs ∈ S)) {true} :=
        jointLaw_true_mono _ _ _ _ fun q D h ↦ by
          simp only [decide_eq_true_eq] at h ⊢
          exact hES q _ h.1 h.2
    _ = _ := jointLaw_dbs_eq_eventWeight S _ _ ρ
    _ ≤ _ := eventWeight_spongeCompressedRuntime_le S hup hempty hε _ _ htot ρ

end fixedPerm

/-! ## The end theorems -/

section main

variable {X Z Y : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

variable (X Z) in
/-- The fraction of the permutations of `X × Z` that are not `PermGood π G`. -/
noncomputable def permBadFrac (G : ℕ) : ℝ≥0∞ :=
  ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
    Fintype.card (Equiv.Perm (X × Z))

variable (X Z) in
/-- The bound of `prob_not_permGood_le` on `permBadFrac X Z (3 s)`. -/
noncomputable def permBadBound (s : ℕ) : ℝ :=
  (Fintype.card X : ℝ) ^ 2 * (Fintype.card Z).choose s *
      ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s +
    (Fintype.card X : ℝ) ^ 2 * Fintype.card Z * (Fintype.card Z).choose s *
      ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s

omit [AddCommGroup X] in
theorem permBadFrac_le {s : ℕ} (hs : 2 * s < Fintype.card X * Fintype.card Z) :
    permBadFrac X Z (3 * s) ≤ ENNReal.ofReal (permBadBound X Z s) := by
  rw [permBadFrac, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card _),
    ← ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  exact ENNReal.ofReal_le_ofReal (prob_not_permGood_le hs)

/-- The collision bound for one permutation `π` with `PermGood π G`. -/
theorem collision_simulate_le [DecidableEq Y] {L : LocalSig.{u, 0}} {W : QReg → Type}
    {A : QReg} (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msgs : (Σ u, W u) → List X × List X) {l : ℕ}
    (hm : ∀ p, (msgs p).1 ≠ [] ∧ (msgs p).2 ≠ [])
    (hl : ∀ p, (msgs p).1.length ≤ l ∧ (msgs p).2.length ≤ l) (out : X → Y) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {π : Equiv.Perm (X × Z)} {G : ℕ}
    (hπ : PermGood π G) :
    spongeEvalDistMap .instruments (simulate I π x) ρ (fun t p ↦ decide ((msgs p).1 ≠ (msgs p).2 ∧
        out (spongeHash (spongePerm t π) (msgs p).1) =
          out (spongeHash (spongePerm t π) (msgs p).2))) {true} ≤
      6 * ((6 * q + 6 * l : ℕ) : ℝ≥0∞) ^ 2 *
          collisionRateBound (X := X) (Z := Z) (6 * q + 6 * l) G F +
        ENNReal.ofReal (2 * (2 * l / Fintype.card X + 4 * l / Fintype.card Z)) := by
  classical
  have herr : (2 * (((2 * l : ℕ) : ℝ) / Fintype.card X +
      (((2 * l : ℕ) : ℝ) + ((2 * l : ℕ) : ℝ)) / Fintype.card Z)) =
      2 * (2 * l / Fintype.card X + 4 * l / Fintype.card Z) := by
    push_cast
    ring
  have h := spongeEvalDistMap_le_of_reads (simulate I π x) (isQueryBound_simulate I π hx)
    (fun p ↦ pairReads π (msgs p)) (lr := 2 * l)
    (fun p i ↦ (isQueryBoundP_pairReads π (msgs p) i).mono (by have := hl p; omega)) ρ
    (fun t p ↦ decide ((msgs p).1 ≠ (msgs p).2 ∧
      out (spongeHash (spongePerm t π) (msgs p).1) = out (spongeHash (spongePerm t π) (msgs p).2)))
    (fun r ↦ IsTranscript (pairReads π (msgs ⟨r.1, r.2.1⟩)) r.2.2 ∧
      (msgs ⟨r.1, r.2.1⟩).1 ≠ (msgs ⟨r.1, r.2.1⟩).2 ∧ out r.2.2.1.1 = out r.2.2.1.2)
    (fun t ⟨u, w⟩ ↦ by
      obtain ⟨h₁, -⟩ := logRun_pairReads π t (msgs ⟨u, w⟩)
      rw [decide_eq_true_iff]
      exact ⟨fun h ↦ ⟨isTranscript_logRun _ _, h.1, by rw [h₁]; exact h.2⟩,
        fun h ↦ ⟨h.2.1, by rw [h₁] at h; exact h.2.2⟩⟩)
    (CollisionBad π out) upClosed_collisionBad not_mem_collisionBad_emptyDbs
    (fun ⟨u, w, r⟩ D hE hD ↦ collisionBad_of_isTranscript π (hm _).1 (hm _).2 hE.2.1 hE.1 hE.2.2 hD)
    (le_of_eq (by ring)) (freshBound_collisionBad hπ hF (6 * q + 6 * l))
  rwa [herr] at h

/-- The preimage bound for one permutation `π` with `PermGood π G`. -/
theorem preimage_simulate_le {L : LocalSig.{u, 0}} {W : QReg → Type} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msg : (Σ u, W u) → List X) {l : ℕ}
    (hm : ∀ p, msg p ≠ []) (hl : ∀ p, (msg p).length ≤ l) (out : X → Y) [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (y0 : Y)
    {π : Equiv.Perm (X × Z)} {G : ℕ} (hπ : PermGood π G) :
    spongeEvalDistMap .instruments (simulate I π x) ρ
        (fun t p ↦ decide (out (spongeHash (spongePerm t π) (msg p)) = y0)) {true} ≤
      6 * ((6 * q + 3 * l : ℕ) : ℝ≥0∞) ^ 2 *
          preimageRateBound (X := X) (Z := Z) (6 * q + 3 * l) G F +
        ENNReal.ofReal (2 * (l / Fintype.card X + 2 * l / Fintype.card Z)) := by
  classical
  have herr : (2 * ((l : ℝ) / Fintype.card X + ((l : ℝ) + (l : ℝ)) / Fintype.card Z)) =
      2 * (l / Fintype.card X + 2 * l / Fintype.card Z) := by
    ring
  have h := spongeEvalDistMap_le_of_reads (simulate I π x) (isQueryBound_simulate I π hx)
    (fun p ↦ spongeEvalM π readHQ readKQ readK'Q (msg p)) (lr := l)
    (fun p i ↦ (isQueryBoundP_spongeEvalM π (msg p) i).mono (hl p)) ρ
    (fun t p ↦ decide (out (spongeHash (spongePerm t π) (msg p)) = y0))
    (fun r ↦ IsTranscript (spongeEvalM π readHQ readKQ readK'Q (msg ⟨r.1, r.2.1⟩)) r.2.2 ∧
      out r.2.2.1 = y0)
    (fun t ⟨u, w⟩ ↦ by
      obtain ⟨h₁, -⟩ := logRun_spongeEvalM π t (msg ⟨u, w⟩)
      rw [decide_eq_true_iff]
      exact ⟨fun h ↦ ⟨isTranscript_logRun _ _, by rw [h₁]; exact h⟩,
        fun h ↦ by rw [h₁] at h; exact h.2⟩)
    (PreimageBad π out y0) (upClosed_preimageBad y0) (not_mem_preimageBad_emptyDbs y0)
    (fun ⟨u, w, r⟩ D hE hD ↦ preimageBad_of_isTranscript π (hm _) hE.1 hE.2 hD)
    (le_of_eq (by ring)) (freshBound_preimageBad hπ (fun y ↦ by convert hF y) y0 (6 * q + 3 * l))
  rwa [herr] at h

/-- **Collision resistance of the sponge in the QRPM**, for any goodness bound `G`. A program
making at most `q` calls of `φ` and `φ⁻¹`, naming at its leaf `p` two nonempty messages of at most
`l` blocks, outputs a collision of `out ∘ spongeHash φ` with probability at most
`permBadFrac G + 6 T² ε + 2 (2 l / |X| + 4 l / |Z|)`, with `T = 6 q + 6 l` and
`ε = collisionRateBound T G F`, where `F` bounds the fibers of `out`. -/
theorem qrpm_sponge_collision_le_permBadFrac [DecidableEq Y] {L : LocalSig.{u, 0}}
    {W : QReg → Type} {A : QReg} (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A)
    {q : ℕ} (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msgs : (Σ u, W u) → List X × List X)
    {l : ℕ} (hm : ∀ p, (msgs p).1 ≠ [] ∧ (msgs p).2 ≠ [])
    (hl : ∀ p, (msgs p).1.length ≤ l ∧ (msgs p).2.length ≤ l) (out : X → Y) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (G : ℕ) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide ((msgs p).1 ≠ (msgs p).2 ∧
        out (spongeHash φ (msgs p).1) = out (spongeHash φ (msgs p).2))) {true} ≤
      permBadFrac X Z G +
        (6 * ((6 * q + 6 * l : ℕ) : ℝ≥0∞) ^ 2 *
            collisionRateBound (X := X) (Z := Z) (6 * q + 6 * l) G F +
          ENNReal.ofReal (2 * (2 * l / Fintype.card X + 4 * l / Fintype.card Z))) := by
  rw [qrpmEvalDistMap_eq_simulate, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply]
  exact average_le _ (fun π ↦ spongeEvalDistMap_apply_le_one _ _ _ _ _)
    fun π hπ ↦ collision_simulate_le I x hx ρ msgs hm hl out hF hπ

/-- **Collision resistance of the sponge in the QRPM** (Corollary 6.13). A program making at most
`q` calls of `φ` and `φ⁻¹`, naming at its leaf `p` two nonempty messages of at most `l` blocks,
outputs a collision of `out ∘ spongeHash φ` with probability at most
`permBadBound s + 6 T² ε + 2 (2 l / |X| + 4 l / |Z|)`, with `T = 6 q + 6 l` and
`ε = collisionRateBound T (3 s) F`, for any `s` with `2 s < |X| |Z|`, where `F` bounds the fibers
of `out`. -/
theorem qrpm_sponge_collision_le [DecidableEq Y] {L : LocalSig.{u, 0}} {W : QReg → Type}
    {A : QReg} (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msgs : (Σ u, W u) → List X × List X) {l : ℕ}
    (hm : ∀ p, (msgs p).1 ≠ [] ∧ (msgs p).2 ≠ [])
    (hl : ∀ p, (msgs p).1.length ≤ l ∧ (msgs p).2.length ≤ l) (out : X → Y) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {s : ℕ}
    (hs : 2 * s < Fintype.card X * Fintype.card Z) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide ((msgs p).1 ≠ (msgs p).2 ∧
        out (spongeHash φ (msgs p).1) = out (spongeHash φ (msgs p).2))) {true} ≤
      ENNReal.ofReal (permBadBound X Z s) +
        (6 * ((6 * q + 6 * l : ℕ) : ℝ≥0∞) ^ 2 *
            collisionRateBound (X := X) (Z := Z) (6 * q + 6 * l) (3 * s) F +
          ENNReal.ofReal (2 * (2 * l / Fintype.card X + 4 * l / Fintype.card Z))) :=
  (qrpm_sponge_collision_le_permBadFrac I x hx ρ msgs hm hl out hF (3 * s)).trans
    (add_le_add_left (permBadFrac_le hs) _)

/-- **Preimage resistance of the sponge in the QRPM**, for any goodness bound `G`. A program
making at most `q` calls of `φ` and `φ⁻¹`, naming at its leaf `p` a nonempty message of at most
`l` blocks, outputs a preimage of `y0` under `out ∘ spongeHash φ` with probability at most
`permBadFrac G + 6 T² ε + 2 (l / |X| + 2 l / |Z|)`, with `T = 6 q + 3 l` and
`ε = preimageRateBound T G F`, where `F` bounds the fibers of `out`. -/
theorem qrpm_sponge_preimage_le_permBadFrac {L : LocalSig.{u, 0}} {W : QReg → Type} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msg : (Σ u, W u) → List X) {l : ℕ}
    (hm : ∀ p, msg p ≠ []) (hl : ∀ p, (msg p).length ≤ l) (out : X → Y) [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (y0 : Y) (G : ℕ) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide (out (spongeHash φ (msg p)) = y0)) {true} ≤
      permBadFrac X Z G +
        (6 * ((6 * q + 3 * l : ℕ) : ℝ≥0∞) ^ 2 *
            preimageRateBound (X := X) (Z := Z) (6 * q + 3 * l) G F +
          ENNReal.ofReal (2 * (l / Fintype.card X + 2 * l / Fintype.card Z))) := by
  rw [qrpmEvalDistMap_eq_simulate, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply]
  exact average_le _ (fun π ↦ spongeEvalDistMap_apply_le_one _ _ _ _ _)
    fun π hπ ↦ preimage_simulate_le I x hx ρ msg hm hl out hF y0 hπ

/-- **Preimage resistance of the sponge in the QRPM** (Corollary 6.14). A program making at most
`q` calls of `φ` and `φ⁻¹`, naming at its leaf `p` a nonempty message of at most `l` blocks,
outputs a preimage of `y0` under `out ∘ spongeHash φ` with probability at most
`permBadBound s + 6 T² ε + 2 (l / |X| + 2 l / |Z|)`, with `T = 6 q + 3 l` and
`ε = preimageRateBound T (3 s) F`, for any `s` with `2 s < |X| |Z|`, where `F` bounds the fibers
of `out`. -/
theorem qrpm_sponge_preimage_le {L : LocalSig.{u, 0}} {W : QReg → Type} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msg : (Σ u, W u) → List X) {l : ℕ}
    (hm : ∀ p, msg p ≠ []) (hl : ∀ p, (msg p).length ≤ l) (out : X → Y) [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (y0 : Y) {s : ℕ}
    (hs : 2 * s < Fintype.card X * Fintype.card Z) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide (out (spongeHash φ (msg p)) = y0)) {true} ≤
      ENNReal.ofReal (permBadBound X Z s) +
        (6 * ((6 * q + 3 * l : ℕ) : ℝ≥0∞) ^ 2 *
            preimageRateBound (X := X) (Z := Z) (6 * q + 3 * l) (3 * s) F +
          ENNReal.ofReal (2 * (l / Fintype.card X + 2 * l / Fintype.card Z))) :=
  (qrpm_sponge_preimage_le_permBadFrac I x hx ρ msg hm hl out hF y0 (3 * s)).trans
    (add_le_add_left (permBadFrac_le hs) _)

end main

/-! ## Keccak-256 -/

section Keccak

/-- At the concrete Keccak-256 types, `permBadFrac` with `G = 18` is at most `2^-777`. -/
theorem keccak256_permBadFrac_le :
    permBadFrac KeccakRate KeccakCapacity 18 ≤ ENNReal.ofReal (1 / 2 ^ 777) := by
  rw [permBadFrac, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Fintype.card _),
    ← ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  exact ENNReal.ofReal_le_ofReal keccak256_prob_not_permGood

/-- **Keccak-256 collisions in the QRPM.** A program making at most `q` calls of the
permutation and its inverse, naming at its leaf two nonempty messages of at most `l` blocks, with
`6 q + 6 l ≤ 2^63`, outputs a collision of Keccak-256 with probability at most
`2^-777 + 2^-64 + 2 (2 l / 2^1088 + 4 l / 2^512)`. -/
theorem keccak256_qrpm_collision_le {L : LocalSig.{u, 0}} {W : QReg → Type} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qrpmSpec (KeccakRate × KeccakCapacity)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A)
    (msgs : (Σ u, W u) → List KeccakRate × List KeccakRate) {l : ℕ}
    (hm : ∀ p, (msgs p).1 ≠ [] ∧ (msgs p).2 ≠ [])
    (hl : ∀ p, (msgs p).1.length ≤ l ∧ (msgs p).2.length ≤ l) (hT : 6 * q + 6 * l ≤ 2 ^ 63) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide ((msgs p).1 ≠ (msgs p).2 ∧
        keccakOut (spongeHash φ (msgs p).1) = keccakOut (spongeHash φ (msgs p).2))) {true} ≤
      ENNReal.ofReal (1 / 2 ^ 777) +
        ((2 ^ 64)⁻¹ + ENNReal.ofReal (2 * (2 * l / 2 ^ 1088 + 4 * l / 2 ^ 512))) := by
  have h := qrpm_sponge_collision_le_permBadFrac I x hx ρ msgs hm hl keccakOut
    (fun y ↦ (card_keccakOut_fiber y).le) 18
  rw [card_keccakRate, card_keccakCapacity, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans (add_le_add keccak256_permBadFrac_le (add_le_add ?_ le_rfl))
  exact keccak_collision_weight_le_two_pow_63 card_keccakRate card_keccakCapacity hT

/-- **Keccak-256 preimages in the QRPM.** A program making at most `q` calls of the permutation
and its inverse, naming at its leaf a nonempty message of at most `l` blocks, with
`6 q + 3 l ≤ 2^64`, outputs a preimage of `y0` under Keccak-256 with probability at most
`2^-777 + 2^-125 + 2 (l / 2^1088 + 2 l / 2^512)`. -/
theorem keccak256_qrpm_preimage_le {L : LocalSig.{u, 0}} {W : QReg → Type} {A : QReg}
    (I : L.Interp) (x : QuantumComp L (qrpmSpec (KeccakRate × KeccakCapacity)) W A) {q : ℕ}
    (hx : x.IsTotalQueryBound q) (ρ : SubState A) (msg : (Σ u, W u) → List KeccakRate) {l : ℕ}
    (hm : ∀ p, msg p ≠ []) (hl : ∀ p, (msg p).length ≤ l) (y0 : Fin 256 → ZMod 2)
    (hT : 6 * q + 3 * l ≤ 2 ^ 64) :
    qrpmEvalDistMap I x ρ (fun φ p ↦ decide (keccakOut (spongeHash φ (msg p)) = y0)) {true} ≤
      ENNReal.ofReal (1 / 2 ^ 777) +
        ((2 ^ 125)⁻¹ + ENNReal.ofReal (2 * (l / 2 ^ 1088 + 2 * l / 2 ^ 512))) := by
  have h := qrpm_sponge_preimage_le_permBadFrac I x hx ρ msg hm hl keccakOut
    (fun y ↦ (card_keccakOut_fiber y).le) y0 18
  rw [card_keccakRate, card_keccakCapacity, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans (add_le_add keccak256_permBadFrac_le (add_le_add ?_ le_rfl))
  exact keccak_preimage_weight_le_two_pow_64 card_keccakRate card_keccakCapacity hT

end Keccak

end Quantum.Sponge

end
