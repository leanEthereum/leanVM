module

public import Quantum.Sponge.Reads
public import Quantum.Sponge.Oracle.Hardwired.Average

@[expose] public section

/-!
# Classical reads with hardwired cells

The fundamental-lemma step of `Quantum.Sponge.spongeEvalDistMap_withReads_le` for the functions
`overwrite W t`, with hardwired cells `W` and uniform `t`, run as the block oracle `hwBlock X Z W`
of the hardwired runtime (`withReads_hardwired_le`). The databases are measured together with
the hardwired cells: an event of the leaf, the result and the read log has probability at most its
probability jointly with "the hardwired cells over the measured databases (`hwView W D`) hold every
logged answer", plus `2 (l_h / |X| + (l_k + l_k') / |Z|)`.

Reads at hardwired cells are exact: they contribute neither to the error nor to the consistency
scalar. Both the functions consistent with a log and the databases agreeing with it factor into
the constant condition that the log agrees with `W` on its hardwired cells, and the condition on
the free part `freeLog W log` (`logProjector_overwrite`, `diagonal_agrees_hwView`), so the
sandwich identity is that of the free part (`hw_sandwich`).
-/

open Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ENNReal NNReal

namespace Quantum.Sponge

open Quantum

variable {X Z : Type}

/-! ## Hardwired and free log entries -/

/-- The entries of a log at cells that are not hardwired in `W`. -/
def freeLog (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) : QueryLog (spongeOSpec X Z) :=
  log.filter fun e ↦ (dbAns W e.1).isNone

/-- Every entry of a log at a hardwired cell of `W` holds the hardwired value. -/
def HwAgrees (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) : Prop :=
  ∀ e ∈ log, (dbAns W e.1).isSome → dbAns W e.1 = some e.2

theorem spongeAns_overwrite (W : Hw X Z) (t : (Z → X) × (X → Z) × (X → Z))
    (q : SpongeQuery X Z) : spongeAns (overwrite W t) q = (dbAns W q).getD (spongeAns t q) := by
  cases q <;> rfl

theorem dbAns_hwView (W : Hw X Z) (D : DbReg X Z) (q : SpongeQuery X Z) :
    dbAns (hwView W D) q = (dbAns W q).or (dbAns D q) := by
  cases q <;> rfl

/-- A condition on every entry of a log splits into the hardwired and the free entries. -/
theorem forall_log_iff (W : Hw X Z) (log : QueryLog (spongeOSpec X Z))
    (P : ((q : SpongeQuery X Z) × spongeOSpec X Z q) → Prop)
    (hP : ∀ e, (dbAns W e.1).isSome → (P e ↔ dbAns W e.1 = some e.2)) :
    (∀ e ∈ log, P e) ↔ HwAgrees W log ∧ ∀ e ∈ freeLog W log, P e := by
  simp only [HwAgrees, freeLog, List.mem_filter, Option.isNone_iff_eq_none]
  constructor
  · intro h
    exact ⟨fun e he hs ↦ (hP e hs).mp (h e he), fun e he ↦ h e he.1⟩
  · rintro ⟨h₁, h₂⟩ e he
    by_cases hs : (dbAns W e.1).isSome
    · exact (hP e hs).mpr (h₁ e he hs)
    · exact h₂ e ⟨he, by simpa using hs⟩

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

instance (W : Hw X Z) : DecidablePred (HwAgrees W) :=
  fun log ↦ inferInstanceAs (Decidable (∀ e ∈ log, (dbAns W e.1).isSome → dbAns W e.1 = some e.2))

instance (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    DecidablePred fun D : DbReg X Z ↦ DbReg.Agrees log (hwView W D) :=
  fun D ↦ inferInstanceAs (Decidable (DbReg.Agrees log (hwView W D)))

/-- The functions `overwrite W t` consistent with a log: those whose free part is consistent with
the free entries, when the log agrees with `W`. -/
theorem logProjector_overwrite (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    logProjector (fun t ↦ spongeAns (overwrite W t)) log =
      (if HwAgrees W log then (1 : ℂ) else 0) • logProjector spongeAns (freeLog W log) := by
  simp only [logProjector, ← diagonal_smul]
  congr 1
  funext t
  have h := forall_log_iff W log (fun e ↦ spongeAns (overwrite W t) e.1 = e.2) fun e hs ↦ by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    simp only [spongeAns_overwrite, hv, Option.getD_some, Option.some.injEq]
  have hf : (∀ e ∈ freeLog W log, spongeAns (overwrite W t) e.1 = e.2) ↔
      ∀ e ∈ freeLog W log, spongeAns t e.1 = e.2 := by
    refine forall₂_congr fun e he ↦ ?_
    have hn : dbAns W e.1 = none := by
      simpa [freeLog, Option.isNone_iff_eq_none] using (List.mem_filter.mp he).2
    rw [spongeAns_overwrite, hn, Option.getD_none]
  rw [hf] at h
  by_cases h₁ : HwAgrees W log <;> by_cases h₂ : ∀ e ∈ freeLog W log, spongeAns t e.1 = e.2 <;>
    simp [h, h₁, h₂]

/-- The databases whose view agrees with a log: those agreeing with its free entries, when the
log agrees with `W`. -/
theorem diagonal_agrees_hwView (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    diagonal (fun D : DbReg X Z ↦ if DbReg.Agrees log (hwView W D) then (1 : ℂ) else 0) =
      (if HwAgrees W log then (1 : ℂ) else 0) •
        diagonal (fun D : DbReg X Z ↦ if DbReg.Agrees (freeLog W log) D then (1 : ℂ) else 0) := by
  rw [← diagonal_smul]
  congr 1
  funext D
  have h := forall_log_iff W log (fun e ↦ dbAns (hwView W D) e.1 = some e.2) fun e hs ↦ by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    simp only [dbAns_hwView, hv, Option.some_or]
  have hf : (∀ e ∈ freeLog W log, dbAns (hwView W D) e.1 = some e.2) ↔
      ∀ e ∈ freeLog W log, dbAns D e.1 = some e.2 := by
    refine forall₂_congr fun e he ↦ ?_
    have hn : dbAns W e.1 = none := by
      simpa [freeLog, Option.isNone_iff_eq_none] using (List.mem_filter.mp he).2
    rw [dbAns_hwView, hn, Option.none_or]
  rw [hf] at h
  by_cases hA : DbReg.Agrees log (hwView W D)
  · have h' := h.mp hA
    have h₂ : DbReg.Agrees (freeLog W log) D := h'.2
    simp [hA, h'.1, h₂]
  · by_cases h₁ : HwAgrees W log
    · have h₂ : ¬ DbReg.Agrees (freeLog W log) D := fun h₂ ↦ hA (h.mpr ⟨h₁, h₂⟩)
      simp [hA, h₁, h₂]
    · simp [hA, h₁]

variable [Nonempty X] [Nonempty Z]

/-- **The sandwich identity with hardwired cells**: the scalar is that of the free entries. -/
theorem hw_sandwich (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    logProjector (fun t ↦ spongeAns (overwrite W t)) log *
        (compressDbs X Z * basisMatrix (ofFunDbs (X := X) (Z := Z)))ᴴ *
        diagonal (fun D : DbReg X Z ↦ if DbReg.Agrees log (hwView W D) then (1 : ℂ) else 0) *
        (compressDbs X Z * basisMatrix (ofFunDbs (X := X) (Z := Z))) *
        logProjector (fun t ↦ spongeAns (overwrite W t)) log =
      (spongeScalar X Z (freeLog W log) : ℂ) •
        logProjector (fun t ↦ spongeAns (overwrite W t)) log := by
  rw [logProjector_overwrite, diagonal_agrees_hwView]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [sponge_sandwich, smul_smul]
  congr 1
  split_ifs <;> ring

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty X] [Nonempty Z] in
/-- Filtering a log lowers its read counts. -/
theorem readCount_freeLog_le (W : Hw X Z) (port : SpongePort) (log : QueryLog (spongeOSpec X Z)) :
    readCount port (freeLog W log) ≤ readCount port log :=
  (List.filter_sublist).countP_le

/-! ## The block oracle and its purification -/

variable [AddCommGroup X] [AddCommGroup Z]

omit [Nonempty X] [Nonempty Z] in
/-- Against the purified oracle of the overwritten functions, a classical read reporting `c`
projects onto the triples whose overwritten functions answer `c`. -/
theorem branch_run₂_spongeReadImpl_hw (W : Hw X Z) (B : QReg) (q : SpongeQuery X Z)
    (c : spongeOSpec X Z q) :
    ((spongePurifiedHw X Z W).toRuntime.run₂ .instruments (spongeReadImpl X Z B q)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        readProjector (fun t ↦ spongeAns (overwrite W t)) q c) := by
  cases q with
  | h z =>
    change ((spongePurifiedHw X Z W).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .h B (z, (0 : X))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B
      (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).1) z c
  | k x =>
    change ((spongePurifiedHw X Z W).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B
      (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.1) x c
  | k' x =>
    change ((spongePurifiedHw X Z W).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k' B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B
      (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.2) x c

omit [Nonempty X] [Nonempty Z] in
/-- Tabulating and compressing intertwines the purified oracle of the overwritten functions with
the block oracle. -/
theorem hwBlock_step_intertwine (W : Hw X Z) (i : SpongePort) (r : Unit) :
    ((hwBlock X Z W).toRuntime.step i).branch r ∘ₗ
        (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft ((spongeSpec X Z).In i) =
      (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((spongePurifiedHw X Z W).toRuntime.step i).branch r := by
  change MatrixMap.conj ((hwBlock X Z W).U i) ∘ₗ
      (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft (spongeIn X Z i) =
    (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft (spongeIn X Z i) ∘ₗ
      MatrixMap.conj ((spongePurifiedHw X Z W).U i)
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    hwBlock_U_mul_one_kronecker]

/-- **Classical reads with hardwired cells are recorded.** A program `x` over the sponge ports,
followed at each leaf `p` by classical reads `oa p` making at most `l_h`, `l_k`, `l_k'` queries of
`h`, `k`, `k'`, run against the hardwired oracle with cells `W`: every event `E` of the leaf, the
result and the read log has probability at most its probability jointly with the hardwired cells
over the measured databases holding every logged answer, plus `2 (l_h / |X| + (l_k + l_k') / |Z|)`.
By `evalDistMap_hwBlock`, the left side is the experiment with the functions `overwrite W t` for
uniform `t`. -/
theorem withReads_hardwired_le (W : Hw X Z) {Wl : QReg → Type} {A : QReg} {β : Type}
    (x : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) Wl A)
    (oa : (Σ u, Wl u) → OracleComp (spongeOSpec X Z) β) {lh lk lk' : ℕ}
    (hh : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .h) lh)
    (hk : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k) lk)
    (hk' : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k') lk')
    (ρ : SubState A) (E : (Σ u, Wl u × β × QueryLog (spongeOSpec X Z)) → Prop)
    [DecidablePred E] :
    (hwBlock X Z W).toRuntime.evalDistMap .instruments (withReads x (spongeReadImpl X Z) oa) ρ
        (fun q ↦ decide (E q)) {true} ≤
      jointLaw (hwBlock X Z W).toRuntime .instruments (withReads x (spongeReadImpl X Z) oa) ρ
          (fun q D ↦ decide (E q ∧ DbReg.Agrees q.2.2.2 (hwView W D))) {true} +
        ENNReal.ofReal (readError X Z lh lk lk') :=
  evalDistMap_withReads_le (spongePurifiedHw X Z W).toRuntime (hwBlock X Z W).toRuntime
    (tabulateDbs X Z) conjTranspose_tabulateDbs_mul_self (hwBlock_step_intertwine W)
    conj_tabulateDbs_init (fun t ↦ spongeAns (overwrite W t)) (spongeReadImpl X Z)
    (branch_run₂_spongeReadImpl_hw W) (fun log D ↦ DbReg.Agrees log (hwView W D))
    (fun log ↦ spongeScalar X Z (freeLog W log)) (hw_sandwich W) x oa ρ _
    (fun p _r hr ↦ one_sub_readError_le_spongeScalar
      ((readCount_freeLog_le W _ _).trans (hr.countP_le (hh p)))
      ((readCount_freeLog_le W _ _).trans (hr.countP_le (hk p)))
      ((readCount_freeLog_le W _ _).trans (hr.countP_le (hk' p)))) E

end Quantum.Sponge

end
