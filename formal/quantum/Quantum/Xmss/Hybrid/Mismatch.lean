module

public import Quantum.Xmss.Hybrid.Graded

@[expose] public section

/-!
# Two realizations of a template that agree off a set of coordinates

Two hidden-value families `v`, `v'` agreeing off a set `B` of hidden coordinates realize one
template program `y` (`realizeT`) into two programs of `runtimeR`. This file bounds the difference
of their port masses by the mass of the record calls whose recorded set meets `B`
(r0-design, section 6: the randomizer bases of non-first labels).

* **The record mass** (`revW m₀ I B x ρ`): the total trace of the inputs of the record calls of
  `x` whose recorded set meets `B` (`revWt`, `recMeets`).
* **Templates whose reads keep the label** (`KeepsLab`, `ReadKeeps`): along every path every read
  port keeps the memory label; composition lemmas mirror `Disc`'s (`keepsLab_bind`,
  `keepsLab_substitute`, `keepsLab_revealThen`, `keepsLab_progThen`, `keepsLab_readLift`, ...).
* **The view off `B`** (`queryWeight_eq_of_viewBy_off`): from `ViewBy`, the masses of sets of
  register states whose label avoids `B` agree at `v` and `v'`.
* **Labels meeting `B` come from records** (`totalWeight_badW_le`): from states on one memory label
  avoiding `B`, the states whose label meets `B` weigh, summed over the calls of the ports `Q`, at
  most `N` times the trace of the inputs, labelled off `B`, of the record calls meeting `B`
  (`revSet`). Labels are path functions (`StepLab`: only a record changes the label), so the run
  stays on one label until a record meets `B`, and after it the rest of the run is paid by its
  trace (`totalWeight_trace_le_of_isChargeBound'`).
* **The mismatch lemma** (`totalWeight_le_mismatch`): for a template that reveals before it
  programs (`Disc y ∅`) and keeps the label (`KeepsLab y`), a diagonal mass `w = diagMass ∘ C`
  (bounded by the trace) vanishing off the ports `Q`, at most `N` calls of `Q` in `realizeT v y`,
  and an initial state on one label `t₀` disjoint from `B`:
  `totalWeight w (realizeT v y) ρ ≤ totalWeight w (realizeT v' y) ρ + N · revW B (realizeT v' y) ρ`.
  `totalWeight_portMass_le_mismatch`: the instance for Graded's `portMass` (hence `spongeMass`,
  `readMass`). `querySupportedOn_initR`: initial states `σ ⊗ init` are on the label `m₀.1`.
* **Averaging the record mass** (`sum_revW_le`, `uavg_revW_le`): for a program not depending on
  `κ`, sets `B κ` inside a candidate set `J` with each candidate in `B κ` for at most an `ε`
  fraction of the `κ`, and at most `R` candidate labels recorded on every path (`candCharge`), the
  record mass averages to at most `R · ε` times the trace.
-/

open Matrix IPFunctor
open scoped ENNReal ComplexOrder Kronecker

universe u v w w₁ u₁ v₁

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly

/-! ## Weights of a runtime -/

section weights

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- Total weights are monotone in the weight on positive semidefinite inputs. -/
theorem totalWeight_le_totalWeight
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (h : ∀ i σ, σ.PosSemidef → w i σ ≤ w' i σ) (x : QuantumComp L spec Ω A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ R.totalWeight I w' x ρ :=
  ENNReal.tsum_le_tsum fun j ↦ R.queryWeight_mono I h x hρ j

/-- Total weights add up. -/
theorem totalWeight_add_weight (w₁ w₂ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I (fun i σ ↦ w₁ i σ + w₂ i σ) x ρ =
      R.totalWeight I w₁ x ρ + R.totalWeight I w₂ x ρ := by
  show ∑' j, _ = ∑' j, _ + ∑' j, _
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun j ↦ Quantum.Xmss.Hybrid.queryWeight_add R I w₁ w₂ x ρ j

/-- Total weights are homogeneous in the weight. -/
theorem totalWeight_const_mul_weight (c : ℝ≥0∞)
    (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I (fun i σ ↦ c * w i σ) x ρ = c * R.totalWeight I w x ρ := by
  show ∑' j, _ = c * ∑' j, _
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun j ↦ R.queryWeight_const_mul I c x ρ j

/-- Total weights of a finite sum of weights. -/
theorem totalWeight_fintype_sum {K : Type*} [Fintype K]
    (w : K → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I (fun i σ ↦ ∑ k, w k i σ) x ρ = ∑ k, R.totalWeight I (w k) x ρ := by
  show ∑' j, _ = ∑ k, ∑' j, _
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  exact tsum_congr fun j ↦ queryWeight_fintype_sum R I w x ρ j

/-- **Charged traces.** With a charge `κ` and at most `n` charge on every path, the traces of the
inputs of the calls, each weighted by the charge of its port, add up to at most `n` times the
initial trace. -/
theorem totalWeight_chargeTrace_le (κ : spec.Port → ℕ) (x : QuantumComp L spec Ω A) :
    ∀ {n : ℕ}, IFreeM.IsChargeBound x (portCharge κ) n →
      ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
        R.totalWeight I (fun i σ ↦ κ i * ENNReal.ofReal σ.trace.re) x ρ ≤
          n * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ =>
    intro n _ ρ _
    simp
  | primBind _ o k ih =>
    intro n hx ρ hρ
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [totalWeight_primBind]
    calc ∑' b, R.totalWeight I _ (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (n : ℝ≥0∞) * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re :=
          ENNReal.tsum_le_tsum fun b ↦
            ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ)
      _ = n * ∑' b, ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re :=
          ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left
          ((((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ) zero_le
  | queryBind _ i E ℓ k ih =>
    intro n hx ρ hρ
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    rw [totalWeight_queryBind, trace_callInput]
    have hs : ∑' r, R.totalWeight I (fun i σ ↦ κ i * ENNReal.ofReal σ.trace.re) (k r)
        ((R.queryStep i E ℓ).branch r ρ) ≤ ((n - κ i : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re :=
      (ENNReal.tsum_le_tsum fun r ↦ ih r (hx.2 r)
        ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)).trans
        (ENNReal.tsum_mul_left.trans_le (mul_le_mul_of_nonneg_left
          ((R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) zero_le))
    calc _ ≤ κ i * ENNReal.ofReal ρ.trace.re +
          ((n - κ i : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := add_le_add le_rfl hs
      _ = n * ENNReal.ofReal ρ.trace.re := by
          rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hx.1]

end weights

/-! ## The view off a set of coordinates -/

section view

/-- A diagonal mass splits along a set. -/
theorem diagMass_eq_inter_add_diff {α : Type} [Fintype α] (C P : Set α) (σ : Matrix α α ℂ) :
    diagMass C σ = diagMass (C ∩ P) σ + diagMass (C \ P) σ := by
  simp only [diagMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hC : a ∈ C <;> by_cases hP : a ∈ P <;> simp [hC, hP]

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type}
  {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
  {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **The view off `B`.** Under `ViewBy`, for hidden values agreeing off `B`, the masses of sets of
register states whose label avoids `B` agree: split by the label, every label avoiding `B` is a
set of coordinates on which the values agree. -/
theorem queryWeight_eq_of_viewBy_off (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) (hview : ViewBy R I lab x ρ j)
    (B : Finset S) {v v' : (s : S) → D s} (hv : Agree (Finset.univ \ B) v v')
    (C : ∀ i, Set (spec.In i × R.D)) (hC : ∀ i p, p ∈ C i → Disjoint (lab p.2) B) :
    R.queryWeight I (fun i ↦ diagMass (C i)) (x v) (ρ v) j =
      R.queryWeight I (fun i ↦ diagMass (C i)) (x v') (ρ v') j := by
  have hsplit : ∀ u, R.queryWeight I (fun i ↦ diagMass (C i)) (x u) (ρ u) j =
      ∑ T : Finset S, R.queryWeight I (fun i ↦ diagMass (C i ∩ {p | lab p.2 = T})) (x u)
        (ρ u) j := fun u ↦ by
    rw [← queryWeight_fintype_sum]
    refine congrArg (fun w ↦ R.queryWeight I w (x u) (ρ u) j)
      (funext fun i ↦ funext fun σ ↦ ?_)
    exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C i) σ
  rw [hsplit v, hsplit v']
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  by_cases hT : Disjoint T B
  · exact hview T v v' (hv.mono fun s hs ↦
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, Finset.disjoint_left.mp hT hs⟩) _
      fun i p hp ↦ hp.2
  · have h0 : (fun i ↦ diagMass (C i ∩ {p | lab p.2 = T})) = fun _ _ ↦ 0 := by
      funext i σ
      have he : C i ∩ {p | lab p.2 = T} = ∅ := Set.eq_empty_of_forall_notMem fun p hp ↦ by
        refine hT ?_
        rw [← (show lab p.2 = T from hp.2)]
        exact hC i p hp.1
      rw [he]
      exact diagMass_empty σ
    rw [h0, queryWeight_zero_weight, queryWeight_zero_weight]

end view

/-! ## Templates whose reads keep the label -/

section keeps

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} {D : S → Type} {M : Type}
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}}

/-- A read port whose memory update keeps the memory label. -/
def ReadKeeps : HwRead X Z (Finset S × M) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- Runtime 1's reads, lifted, keep the label. -/
theorem readKeeps_liftRead (c : HwRead X Z M) : ReadKeeps (liftRead (S := S) c) := by
  cases c <;> intro _ _ <;> rfl

variable (good) in
/-- A template port keeps the label: a read port keeps it, the other ports impose nothing. -/
def portKeeps : (tmplSpec X Z S D M good).Port → Prop
  | .inl (.inl (.inr c)) => ReadKeeps c.1
  | _ => True

variable (good) in
/-- A command keeps the label. -/
def cmdKeeps {A : QReg} : QuantumComp.Cmd L (tmplSpec X Z S D M good) A → Prop
  | .prim _ => True
  | .query i _ _ => portKeeps good i

/-- **A template whose reads keep the label**: along every path, every read port called keeps the
memory label. -/
def KeepsLab {Ω : QReg → Type w} :
    {A : QReg} → IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A →
      Prop
  | _, .pure _ => True
  | _, .liftBind c next => cmdKeeps good c ∧ ∀ b, KeepsLab (next b)

variable {Ω : QReg → Type w}

theorem keepsLab_cast {A A' : QReg} (e : A = A')
    (y : IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A) :
    KeepsLab (e ▸ y) ↔ KeepsLab y := by
  subst e
  rfl

/-- Sequencing keeps the label. -/
theorem keepsLab_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A)
    (g : ∀ u, Ω u → IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Y u)
    (hx : KeepsLab x) (hg : ∀ u a, KeepsLab (g u a)) : KeepsLab (x.bind g) := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ a => exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem keepsLab₂_bind {A B C : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (tmplSpec X Z S D M good) A B α)
    (g : α → QuantumComp₂ L (tmplSpec X Z S D M good) B C β) (hx : KeepsLab x)
    (hg : ∀ a, KeepsLab (g a)) : KeepsLab (x.bind g) := by
  refine keepsLab_bind x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

theorem keepsLab_primBind {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (tmplSpec X Z S D M good) Ω (L.next o b)) :
    KeepsLab (QuantumComp.primBind o k) ↔ ∀ b, KeepsLab (k b) :=
  ⟨fun h b ↦ h.2 (ULift.up b), fun h ↦ ⟨trivial, fun b ↦ h b.down⟩⟩

theorem keepsLab_queryBind {A : QReg} (i : (tmplSpec X Z S D M good).Port) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In i × E)
    (k : (tmplSpec X Z S D M good).Result i →
      QuantumComp L (tmplSpec X Z S D M good) Ω (QReg.of ((tmplSpec X Z S D M good).Out i × E))) :
    KeepsLab (QuantumComp.queryBind i E ℓ k) ↔ portKeeps good i ∧ ∀ r, KeepsLab (k r) :=
  ⟨fun h ↦ ⟨h.1, fun r ↦ h.2 (ULift.up r)⟩, fun h ↦ ⟨h.1, fun r ↦ h.2 r.down⟩⟩

/-- Substituting trees that keep the label. -/
theorem keepsLab_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)))
    (hσ : ∀ A c, KeepsLab (σ A c)) {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : KeepsLab (x.substitute σ) := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind]
    exact keepsLab_bind _ _ (hσ s c) fun u ans ↦ (keepsLab_cast ans.2 _).mpr (ih ans.1)

theorem keepsLab_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    KeepsLab (QComp.act (spec := tmplSpec X Z S D M good) p) :=
  (keepsLab_primBind _ _).mpr fun _ ↦ trivial

theorem keepsLab_revealThen {B C : QReg} {α : Type} (T₀ : Finset S)
    (k : RevealVals D T₀ × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α)
    (hk : ∀ r, KeepsLab (k r)) : KeepsLab (revealThen good T₀ k) :=
  (keepsLab_queryBind (.inr T₀) B _ _).mpr ⟨trivial, fun r ↦
    keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦ hk r⟩

theorem keepsLab_progThen {B C : QReg} {α : Type} (p : LazyProg X Z S D) (hp : good p)
    (k : QComp (tmplSpec X Z S D M good) B C α) (hk : KeepsLab k) :
    KeepsLab (progThen p hp k) :=
  (keepsLab_queryBind (.inl (.inr ⟨p, hp⟩)) B _ _).mpr ⟨trivial, fun _ ↦
    keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦ hk⟩

/-- Runtime 1's programs keep the label. -/
theorem keepsLab_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    KeepsLab (readLift good y) := by
  induction y using IPFunctor.IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show KeepsLab (IPFunctor.IFreeM.mapLens (readLens good) (IPFunctor.IFreeM.liftBind c next))
    rw [IPFunctor.IFreeM.mapLens_liftBind]
    refine ⟨?_, fun b ↦ (keepsLab_cast _ _).mpr (ih _)⟩
    rcases c with o | ⟨i | c, E, ℓ⟩
    · trivial
    · trivial
    · exact readKeeps_liftRead c

end keeps

/-! ## Labels meeting `B` come from records -/

section bad

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (X Z M) in
/-- A port of `runtimeR` is a record of a set meeting `B`. -/
def recMeets (B : Finset S) : (recHwSpec X Z S M).Port → Bool
  | .inl _ => false
  | .inr T => !decide (Disjoint T B)

/-- The mass of the register states whose memory label meets `B`, at the ports `Q`. -/
noncomputable def badW (B : Finset S) (Q : (recHwSpec X Z S M).Port → Prop) [DecidablePred Q] :
    ∀ i : (recHwSpec X Z S M).Port,
      Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
        ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if Q i then diagMass {p | ¬ Disjoint p.2.2.2.1 B} σ else 0

variable (X Z M) in
/-- The register states, labelled off `B`, at a record meeting `B`; empty at the other ports. -/
def revSet (B : Finset S) (i : (recHwSpec X Z S M).Port) :
    Set ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) :=
  if recMeets X Z M B i then {p | Disjoint p.2.2.2.1 B} else ∅

variable (X Z M) in
/-- The trace at a record meeting `B`, `0` at the other ports. -/
noncomputable def revWt (B : Finset S) :
    ∀ i : (recHwSpec X Z S M).Port,
      Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
        ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if recMeets X Z M B i then ENNReal.ofReal σ.trace.re else 0

/-- **The record mass**: the total trace of the inputs of the record calls of `x` whose recorded
set meets `B`. -/
noncomputable def revW (m₀ : Finset S × M) (I : L.Interp) (B : Finset S) {A : QReg}
    (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) : ℝ≥0∞ :=
  (runtimeR m₀).totalWeight I (revWt X Z M B) x ρ

/-- A step of `runtimeR` at port `i` moves support on the memory label `t` to support on `t'`. -/
def StepLab (m₀ : Finset S × M) (i : (recHwSpec X Z S M).Port) (t t' : Finset S) : Prop :=
  ∀ r (σ : Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ),
    QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)) ↦
      m.2.2.2.1) {t} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z S M).Out i × QReg.of (HwReg X Z (Finset S × M)) ↦
      m.2.2.2.1) {t'} (((runtimeR m₀).step i).branch r σ)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] [Fintype S] [Fintype M] in
/-- A read keeping the label keeps it on every nonzero Kraus entry. -/
theorem hwReadKraus_ne_zero_keeps {c : HwRead X Z (Finset S × M)} (hc : ReadKeeps c)
    (r : c.Result) {u u' : Unit} {s s' : HwReg X Z (Finset S × M)}
    (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.2.1 = s.2.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact (hc _ _).trans (congrArg Prod.fst hp).symm
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact (hc _ _).trans (congrArg Prod.fst hp).symm
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact (hc _ _).trans (congrArg Prod.fst hp).symm

theorem stepLab_sponge (m₀ : Finset S × M) (i : SpongePort) (t : Finset S) :
    StepLab (X := X) (Z := Z) m₀ (.inl (.inl (.inl i))) t t := by
  intro r σ hσ
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  obtain ⟨a, s⟩ := q
  obtain ⟨a', s'⟩ := q'
  show s'.2.2.1 ∈ ({t} : Set (Finset S))
  rw [spongeHardwired_U_ne_zero_snd (hwEmpty X Z) m₀ i hK]
  exact hq

theorem stepLab_read (m₀ : Finset S × M) (c : HwRead X Z (Finset S × M)) (hc : ReadKeeps c)
    (t : Finset S) : StepLab (X := X) (Z := Z) m₀ (.inl (.inl (.inr c))) t t := by
  intro r σ hσ
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  obtain ⟨a, s⟩ := q
  obtain ⟨a', s'⟩ := q'
  show s'.2.2.1 ∈ ({t} : Set (Finset S))
  rw [hwReadKraus_ne_zero_keeps hc r hK]
  exact hq

theorem stepLab_prog (m₀ : Finset S × M) (c : HwProg X Z) (t : Finset S) :
    StepLab (X := X) (Z := Z) m₀ (.inl (.inr c)) t t := by
  intro r σ hσ
  have hb : ((runtimeR (X := X) (Z := Z) m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  obtain ⟨a, s⟩ := q
  obtain ⟨a', s'⟩ := q'
  show s'.2.2.1 ∈ ({t} : Set (Finset S))
  rw [hwProgKraus_ne_zero_snd c r hK]
  exact hq

theorem stepLab_rec (m₀ : Finset S × M) (T t : Finset S) :
    StepLab (X := X) (Z := Z) m₀ (.inr T) t (t ∪ T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have h := recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
    show q'.2.2.2.1 ∈ ({t ∪ T} : Set (Finset S))
    rw [h]
    exact congrArg (· ∪ T) (Set.mem_singleton_iff.mp hq)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- On one label avoiding `B` the states meeting `B` weigh nothing. -/
theorem badW_eq_zero (B : Finset S) (Q : (recHwSpec X Z S M).Port → Prop) [DecidablePred Q]
    (i : (recHwSpec X Z S M).Port) {t : Finset S} (ht : Disjoint t B)
    {σ : Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ}
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))
      ↦ m.2.2.2.1) {t} σ) : badW B Q i σ = 0 := by
  unfold badW
  split_ifs
  · refine Finset.sum_eq_zero fun p _ ↦ ?_
    by_cases hp : p ∈ {p : (recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)) |
        ¬ Disjoint p.2.2.2.1 B}
    · rw [Set.indicator_of_mem hp]
      have h0 : σ p p = 0 := by
        by_contra h0
        refine hp ?_
        have hpt : p.2.2.2.1 = t := Set.mem_singleton_iff.mp (hσ p p h0).1
        rw [hpt]
        exact ht
      simp [h0]
    · exact Set.indicator_of_notMem hp _
  · rfl

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem badW_le (B : Finset S) (Q : (recHwSpec X Z S M).Port → Prop) [DecidablePred Q]
    (i : (recHwSpec X Z S M).Port)
    {σ : Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ} (hσ : σ.PosSemidef) :
    badW B Q i σ ≤ if Q i then ENNReal.ofReal σ.trace.re else 0 := by
  unfold badW
  split_ifs
  · exact diagMass_le _ hσ
  · exact le_rfl

/-- One call that keeps the label off `B`. -/
theorem totalWeight_badW_queryBind_le (m₀ : Finset S × M) (I : L.Interp) (B : Finset S)
    (Q : (recHwSpec X Z S M).Port → Prop) [DecidablePred Q] {A : QReg}
    (i : (recHwSpec X Z S M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    (k : (recHwSpec X Z S M).Result i →
      QuantumComp L (recHwSpec X Z S M) Ω (QReg.of ((recHwSpec X Z S M).Out i × E)))
    {t t' : Finset S} (ht : Disjoint t B) (hstep : StepLab m₀ i t t') {n : ℕ}
    (hk : ∀ r (ρ' : Matrix (QReg.of ((recHwSpec X Z S M).Out i × E) ×
        QReg.of (HwReg X Z (Finset S × M)))
        (QReg.of ((recHwSpec X Z S M).Out i × E) × QReg.of (HwReg X Z (Finset S × M))) ℂ),
      ρ'.PosSemidef →
      QuerySupportedOn (fun p : QReg.of ((recHwSpec X Z S M).Out i × E) ×
        QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t'} ρ' →
      (runtimeR m₀).totalWeight I (badW B Q) (k r) ρ' ≤
        ((n - if Q i then 1 else 0 : ℕ) : ℝ≥0∞) *
          (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i)) (k r) ρ')
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t} ρ) :
    (runtimeR m₀).totalWeight I (badW B Q) (QuantumComp.queryBind i E ℓ k) ρ ≤
      n * (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
        (QuantumComp.queryBind i E ℓ k) ρ := by
  refine ((runtimeR m₀).totalWeight_queryBind I i E ℓ k ρ).trans_le
    (le_trans ?_ (mul_le_mul_of_nonneg_left
      ((runtimeR m₀).totalWeight_queryBind I i E ℓ k ρ).ge zero_le))
  refine (add_le_add (le_of_eq (badW_eq_zero B Q i ht
    (hs.callInput (g := fun s : HwReg X Z (Finset S × M) ↦ s.2.2.1) ℓ))) le_rfl).trans ?_
  refine (zero_add _).le.trans ?_
  calc ∑' r, (runtimeR m₀).totalWeight I (badW B Q) (k r)
        (((runtimeR m₀).queryStep i E ℓ).branch r ρ)
      ≤ ∑' r, (n : ℝ≥0∞) * (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
          (k r) (((runtimeR m₀).queryStep i E ℓ).branch r ρ) :=
        ENNReal.tsum_le_tsum fun r ↦ (hk r _
          (((runtimeR m₀).queryStep i E ℓ).posSemidef_branch_apply r hρ)
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s.2.2.1) i r (hstep r) E ℓ
            hs)).trans
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) zero_le)
    _ = n * ∑' r, (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
          (k r) (((runtimeR m₀).queryStep i E ℓ).branch r ρ) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left le_add_self zero_le

/-- One record call meeting `B`: the rest of the run is paid by its trace. -/
theorem totalWeight_badW_queryBind_rec_le (m₀ : Finset S × M) (I : L.Interp) (B : Finset S)
    (Q : (recHwSpec X Z S M).Port → Prop) [DecidablePred Q] {A : QReg} (T : Finset S)
    (hT : ¬ Disjoint T B) (E : QReg) (ℓ : A ≃ (recHwSpec X Z S M).In (.inr T) × E)
    (k : (recHwSpec X Z S M).Result (.inr T) →
      QuantumComp L (recHwSpec X Z S M) Ω (QReg.of ((recHwSpec X Z S M).Out (.inr T) × E)))
    {t : Finset S} (ht : Disjoint t B) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge fun i ↦ if Q i then 1 else 0)
      (n - if Q (.inr T) then 1 else 0))
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t} ρ) :
    (runtimeR m₀).totalWeight I (badW B Q) (QuantumComp.queryBind (.inr T) E ℓ k) ρ ≤
      n * (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
        (QuantumComp.queryBind (.inr T) E ℓ k) ρ := by
  have hci := hs.callInput (g := fun s : HwReg X Z (Finset S × M) ↦ s.2.2.1) ℓ
  have hm : recMeets X Z M B (.inr T) = true := by simp [recMeets, hT]
  have h1 : revSet X Z M B (.inr T) = {p | Disjoint p.2.2.2.1 B} := by simp [revSet, hm]
  have hsupp : QuerySupportedOn (fun p : (recHwSpec X Z S M).In (.inr T) ×
      QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t' | Disjoint t' B}
      (callInput ℓ (runtimeR m₀).D ρ) := hci.imp fun m hm' ↦ by
    have h' : m.2.2.2.1 = t := Set.mem_singleton_iff.mp hm'
    show Disjoint m.2.2.2.1 B
    rw [h']
    exact ht
  have hrev : diagMass (revSet X Z M B (.inr T)) (callInput ℓ (runtimeR m₀).D ρ) =
      ENNReal.ofReal ρ.trace.re :=
    (congrArg (fun C ↦ diagMass C (callInput ℓ (runtimeR m₀).D ρ)) h1).trans
      ((diagMass_eq_of_querySupportedOn (posSemidef_callInput ℓ hρ) hsupp).trans
        (congrArg (fun z : ℂ ↦ ENNReal.ofReal z.re) (trace_callInput ℓ ρ)))
  refine ((runtimeR m₀).totalWeight_queryBind I (.inr T) E ℓ k ρ).trans_le
    (le_trans ?_ (mul_le_mul_of_nonneg_left
      ((runtimeR m₀).totalWeight_queryBind I (.inr T) E ℓ k ρ).ge zero_le))
  refine (add_le_add (le_of_eq (badW_eq_zero B Q _ ht hci)) le_rfl).trans ?_
  refine (zero_add _).le.trans ?_
  calc ∑' r, (runtimeR m₀).totalWeight I (badW B Q) (k r)
        (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ)
      ≤ ∑' r, ((n - if Q (.inr T) then 1 else 0 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ).trace.re :=
        ENNReal.tsum_le_tsum fun r ↦
          (totalWeight_le_totalWeight _ I (fun i σ hσ ↦ badW_le B Q i hσ) (k r)
            (((runtimeR m₀).queryStep (.inr T) E ℓ).posSemidef_branch_apply r hρ)).trans
          (totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I Q (k r) (hk r)
            (((runtimeR m₀).queryStep (.inr T) E ℓ).posSemidef_branch_apply r hρ))
    _ ≤ ∑' r, (n : ℝ≥0∞) *
          ENNReal.ofReal (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ).trace.re :=
        ENNReal.tsum_le_tsum fun r ↦
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) zero_le
    _ = n * ∑' r,
          ENNReal.ofReal (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ).trace.re :=
        ENNReal.tsum_mul_left
    _ ≤ n * ENNReal.ofReal ρ.trace.re := mul_le_mul_of_nonneg_left
        (((runtimeR m₀).queryStep (.inr T) E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) zero_le
    _ = n * diagMass (revSet X Z M B (.inr T)) (callInput ℓ (runtimeR m₀).D ρ) := by rw [hrev]
    _ ≤ _ := mul_le_mul_of_nonneg_left le_self_add zero_le

variable {S' : Type} [Fintype S'] [DecidableEq S'] {D : S' → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {good : LazyProg X Z S' D → Prop}

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- **Labels meeting `B` come from records.** From states on one memory label avoiding `B`, with
at most `n` calls of the ports `Q`, the masses of the states whose label meets `B` at the calls of
`Q` add up to at most `n` times the masses, labelled off `B`, of the record calls meeting `B`. -/
theorem totalWeight_badW_le (m₀ : Finset S' × M) (I : L.Interp) (B : Finset S')
    (Q : (recHwSpec X Z S' M).Port → Prop) [DecidablePred Q] (v : (s : S') → D s) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S' D M good) Ω A) (hy : KeepsLab y) :
    ∀ (n : ℕ) (t : Finset S'), Disjoint t B →
      ∀ ρ : Matrix (A × QReg.of (HwReg X Z (Finset S' × M)))
        (A × QReg.of (HwReg X Z (Finset S' × M))) ℂ, ρ.PosSemidef →
      QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S' × M)) ↦ p.2.2.2.1) {t} ρ →
      IFreeM.IsChargeBound (realizeT v y) (portCharge fun i ↦ if Q i then 1 else 0) n →
      (runtimeR m₀).totalWeight I (badW B Q) (realizeT v y) ρ ≤
        n * (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i)) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ =>
    intro n t _ ρ _ _ _
    exact (le_of_eq ((runtimeR m₀).totalWeight_pure I _ ρ)).trans zero_le
  | primBind _ o k ih =>
    intro n t ht ρ hρ hs hn
    have hn' := (isChargeBound_portCharge_primBind_iff _ o (fun b ↦ realizeT v (k b)) n).mp hn
    refine ((runtimeR m₀).totalWeight_primBind I o (fun b ↦ realizeT v (k b)) ρ).trans_le
      (le_trans ?_ (mul_le_mul_of_nonneg_left
        ((runtimeR m₀).totalWeight_primBind I o (fun b ↦ realizeT v (k b)) ρ).ge zero_le))
    exact (ENNReal.tsum_le_tsum fun b ↦ ih b (hy.2 (ULift.up b)) n t ht _
      (((I o).frame _).posSemidef_branch_apply b hρ)
      (QuerySupportedOn.amplify_snd (q := fun s : HwReg X Z (Finset S' × M) ↦ s.2.2.1) hs _)
      (hn' b)).trans_eq ENNReal.tsum_mul_left
  | queryBind A' i E ℓ k ih =>
    intro n t ht ρ hρ hs hn
    have hκ := fun j ↦ isChargeBound_portCharge_queryBind_iff (A := A')
      (fun i : (recHwSpec X Z S' M).Port ↦ if Q i then 1 else 0) j E (X := Ω) (L := L)
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · have hn' := (hκ (.inl (.inl (.inl i))) ℓ (fun r ↦ realizeT v (k r)) n).mp hn
      exact totalWeight_badW_queryBind_le m₀ I B Q (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) ht (stepLab_sponge m₀ i t)
        (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) _ t ht ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
    · have hn' := (hκ (.inl (.inl (.inr c.1))) ℓ (fun r ↦ realizeT v (k r)) n).mp hn
      exact totalWeight_badW_queryBind_le m₀ I B Q (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) ht (stepLab_read m₀ c.1 hy.1 t)
        (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) _ t ht ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
    · cases p with
      | programH T₀ c =>
        have hn' := (hκ (.inl (.inr ((LazyProg.programH T₀ c).realize v))) ℓ
          (fun r ↦ realizeT v (k r)) n).mp hn
        exact totalWeight_badW_queryBind_le m₀ I B Q
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) ht
          (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) _ t ht ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
      | programK T₀ c =>
        have hn' := (hκ (.inl (.inr ((LazyProg.programK T₀ c).realize v))) ℓ
          (fun r ↦ realizeT v (k r)) n).mp hn
        exact totalWeight_badW_queryBind_le m₀ I B Q
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) ht
          (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) _ t ht ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
      | programK' T₀ c =>
        have hn' := (hκ (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) ℓ
          (fun r ↦ realizeT v (k r)) n).mp hn
        exact totalWeight_badW_queryBind_le m₀ I B Q
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) ht
          (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) _ t ht ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
    · have hn' := (hκ (.inr T) ℓ (fun m ↦ realizeT v (k (restrictTo T v, m))) n).mp hn
      by_cases hTB : Disjoint T B
      · exact totalWeight_badW_queryBind_le m₀ I B Q (.inr T) E ℓ
          (fun m ↦ realizeT v (k (restrictTo T v, m))) ht (stepLab_rec m₀ T t)
          (fun r ρ' hρ' hs' ↦ ih (restrictTo T v, r) (hy.2 (ULift.up (restrictTo T v, r))) _
            (t ∪ T) (Finset.disjoint_union_left.mpr ⟨ht, hTB⟩) ρ' hρ' hs' (hn'.2 r)) ρ hρ hs
      · exact totalWeight_badW_queryBind_rec_le m₀ I B Q T hTB E ℓ
          (fun m ↦ realizeT v (k (restrictTo T v, m))) ht hn'.2 ρ hρ hs

/-- **The mismatch lemma.** Let the template `y` reveal before it programs and keep the label,
and let the hidden values `v`, `v'` agree off `B`. For a diagonal mass `w = diagMass ∘ C`
vanishing off the ports `Q`, with at most `N` calls of `Q` in the run of `realizeT v y`, from an
initial state on one memory label disjoint from `B`, the mass at `v` is at most the mass at `v'`
plus `N` times the record mass of `B` at `v'`. -/
theorem totalWeight_le_mismatch (m₀ : Finset S' × M) (I : L.Interp) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S' D M good) Ω A) (hdisc : Disc y ∅) (hy : KeepsLab y)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S' × M))) (A × QReg.of (HwReg X Z (Finset S' × M)))
      ℂ) (hρ : ρ.PosSemidef) {t₀ : Finset S'}
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S' × M)) ↦ p.2.2.2.1) {t₀} ρ)
    (B : Finset S') (ht₀ : Disjoint t₀ B)
    (Q : (recHwSpec X Z S' M).Port → Prop) [DecidablePred Q]
    (C : ∀ i, Set ((recHwSpec X Z S' M).In i × QReg.of (HwReg X Z (Finset S' × M))))
    (hCQ : ∀ i, ¬ Q i → C i = ∅) {v v' : (s : S') → D s} (hv : Agree (Finset.univ \ B) v v')
    {N : ℕ} (hN : IFreeM.IsChargeBound (realizeT v y) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v y) ρ ≤
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v' y) ρ +
        N * revW m₀ I B (realizeT v' y) ρ := by
  have heq : ∀ C' : ∀ i, Set ((recHwSpec X Z S' M).In i × QReg.of (HwReg X Z (Finset S' × M))),
      (∀ i p, p ∈ C' i → Disjoint p.2.2.2.1 B) →
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C' i)) (realizeT v y) ρ =
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C' i)) (realizeT v' y) ρ := fun C' hC' ↦
    tsum_congr fun j ↦ queryWeight_eq_of_viewBy_off (runtimeR m₀) I (fun r ↦ r.2.2.1)
      (fun u ↦ realizeT u y) (fun _ ↦ ρ) j
      (viewBy_runtimeR_of_disc I m₀ y ∅ hdisc (fun _ ↦ ρ) (lazy_const _ ρ)
        (fun _ ↦ suppAt_empty _ ρ) j) B hv C' hC'
  have hsplit : ∀ u : (s : S') → D s,
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT u y) ρ =
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT u y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT u y) ρ := fun u ↦
    (congrArg (fun w ↦ (runtimeR m₀).totalWeight I w (realizeT u y) ρ)
      (funext fun i ↦ funext fun σ ↦
        diagMass_eq_inter_add_diff (C i) {p | Disjoint p.2.2.2.1 B} σ)).trans
      (totalWeight_add_weight (runtimeR m₀) I _ _ (realizeT u y) ρ)
  have hbad : (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
      (realizeT v y) ρ ≤ (runtimeR m₀).totalWeight I (badW B Q) (realizeT v y) ρ :=
    totalWeight_le_totalWeight _ I (fun i σ _ ↦ by
      show _ ≤ (if Q i then diagMass {p | ¬ Disjoint p.2.2.2.1 B} σ else 0)
      by_cases hQ : Q i
      · simp only [hQ, ↓reduceIte]
        exact diagMass_mono (fun p hp ↦ hp.2) σ
      · simp only [hQ, ↓reduceIte]
        exact le_of_eq (Finset.sum_eq_zero fun p _ ↦ Set.indicator_of_notMem
          (fun hp ↦ Set.notMem_empty p (hCQ i hQ ▸ hp.1)) _)) _ hρ
  have hrevSet : ∀ i p, p ∈ revSet X Z M B i → Disjoint p.2.2.2.1 B := fun i p hp ↦ by
    unfold revSet at hp
    split_ifs at hp
    · exact hp
    · exact hp.elim
  have hrev : (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i)) (realizeT v' y)
      ρ ≤ revW m₀ I B (realizeT v' y) ρ :=
    totalWeight_le_totalWeight _ I (fun i σ hσ ↦ by
      show diagMass (if recMeets X Z M B i then {p | Disjoint p.2.2.2.1 B} else ∅) σ ≤
        (if recMeets X Z M B i then ENNReal.ofReal σ.trace.re else 0)
      split_ifs
      · exact diagMass_le _ hσ
      · exact (diagMass_empty σ).le) _ hρ
  have hb : (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
      (realizeT v y) ρ ≤ N * revW m₀ I B (realizeT v' y) ρ :=
    hbad.trans ((totalWeight_badW_le m₀ I B Q v y hy N t₀ ht₀ ρ hρ hs hN).trans
      (mul_le_mul_of_nonneg_left ((heq (revSet X Z M B) hrevSet).trans_le hrev) zero_le))
  calc (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v y) ρ
      = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ := hsplit v
    _ = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ :=
        congrArg (· + _) (heq (fun i ↦ C i ∩ {p | Disjoint p.2.2.2.1 B}) fun i p hp ↦ hp.2)
    _ ≤ (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ + N * revW m₀ I B (realizeT v' y) ρ := add_le_add le_rfl hb
    _ ≤ ((runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ) + N * revW m₀ I B (realizeT v' y) ρ :=
        add_le_add le_self_add le_rfl
    _ = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v' y) ρ +
        N * revW m₀ I B (realizeT v' y) ρ := congrArg (· + _) (hsplit v').symm

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- Graded's port masses are diagonal masses. -/
theorem portMass_eq_diagMass (Q : (recHwSpec X Z S' M).Port → Prop) [DecidablePred Q]
    (Hh : Set Z) (Hk Hk' : Set X) :
    portMass (S := S') (M' := M) Q Hh Hk Hk' =
      fun i ↦ diagMass (if Q i then extHidSet Hh Hk Hk' i else ∅) := by
  funext i σ
  by_cases hQ : Q i
  · simp only [portMass, hQ, ↓reduceIte]
    exact congrFun (congrFun (extWeight_hiddenMass_eq _ _ _) i) σ
  · simp only [portMass, hQ, ↓reduceIte]
    exact (Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).symm

/-- **The mismatch lemma for Graded's port masses** (`spongeMass`, `readMass`). -/
theorem totalWeight_portMass_le_mismatch (m₀ : Finset S' × M) (I : L.Interp) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S' D M good) Ω A) (hdisc : Disc y ∅) (hy : KeepsLab y)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S' × M))) (A × QReg.of (HwReg X Z (Finset S' × M)))
      ℂ) (hρ : ρ.PosSemidef) {t₀ : Finset S'}
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S' × M)) ↦ p.2.2.2.1) {t₀} ρ)
    (B : Finset S') (ht₀ : Disjoint t₀ B)
    (Q : (recHwSpec X Z S' M).Port → Prop) [DecidablePred Q] (Hh : Set Z) (Hk Hk' : Set X)
    {v v' : (s : S') → D s} (hv : Agree (Finset.univ \ B) v v') {N : ℕ}
    (hN : IFreeM.IsChargeBound (realizeT v y) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') (realizeT v y) ρ ≤
      (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') (realizeT v' y) ρ +
        N * revW m₀ I B (realizeT v' y) ρ := by
  rw [portMass_eq_diagMass]
  exact totalWeight_le_mismatch m₀ I y hdisc hy ρ hρ hs B ht₀ Q _
    (fun i hQ ↦ by simp only [hQ, ↓reduceIte]) hv hN

/-- An initial state `σ ⊗ init` is on the memory label `m₀.1`. -/
theorem querySupportedOn_initR (m₀ : Finset S × M) {A : QReg} (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg X Z (Finset S × M)) ↦ a.2.2.2.1) {m₀.1}
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty X Z, m₀) : HwReg X Z (Finset S × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({m₀.1} : Set (Finset S)) ∧ b.2.2.2.1 ∈ ({m₀.1} : Set (Finset S))
    rw [← he.1, ← he.2]
    exact ⟨rfl, rfl⟩
  · exact absurd rfl h'

end bad

/-! ## Averaging the record mass -/

section avg

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (X Z M) in
/-- The charge of a call: for a record, the number of candidate labels `J` in its set. -/
def candCharge (J : Finset S) : (recHwSpec X Z S M).Port → ℕ
  | .inl _ => 0
  | .inr T => (T ∩ J).card

/-- **The record mass, summed over a coordinate the run ignores.** Let the sets `B κ` lie in the
candidates `J`, each candidate lie in `B κ` for at most `ε |K|` of the `κ`, and every path of `x`
record at most `R` candidates. Then the record masses of the `B κ` add up to at most
`|K| · R · ε` times the trace. -/
theorem sum_revW_le (m₀ : Finset S × M) (I : L.Interp) {A : QReg}
    (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ} (hρ : ρ.PosSemidef) {K : Type*} [Fintype K] (B : K → Finset S) (J : Finset S)
    (hBJ : ∀ κ, B κ ⊆ J) (ε : ℝ≥0∞)
    (hε : ∀ s ∈ J, ((Finset.univ.filter fun κ ↦ s ∈ B κ).card : ℝ≥0∞) ≤ ε * Fintype.card K)
    {R : ℕ} (hR : IFreeM.IsChargeBound x (portCharge (candCharge X Z M J)) R) :
    ∑ κ, revW m₀ I (B κ) x ρ ≤ Fintype.card K * (R * ε * ENNReal.ofReal ρ.trace.re) := by
  have hpoint : ∀ i (σ : Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ),
      ∑ κ, revWt X Z M (B κ) i σ ≤
        ((Fintype.card K : ℝ≥0∞) * ε) * ((candCharge X Z M J i : ℝ≥0∞) *
          ENNReal.ofReal σ.trace.re) := by
    intro i σ
    rcases i with i | T
    · simp [revWt, recMeets]
    · have hstep : ∀ κ, revWt X Z M (B κ) (.inr T) σ ≤
          ∑ s ∈ T ∩ J, if s ∈ B κ then ENNReal.ofReal σ.trace.re else 0 := fun κ ↦ by
        by_cases h : Disjoint T (B κ)
        · simp [revWt, recMeets, h]
        · obtain ⟨s, hsT, hsB⟩ := Finset.not_disjoint_iff.mp h
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum
            (f := fun s ↦ if s ∈ B κ then ENNReal.ofReal σ.trace.re else 0) (fun _ _ ↦ zero_le)
            (Finset.mem_inter.mpr ⟨hsT, hBJ κ hsB⟩))
          simp [revWt, recMeets, h, hsB]
      calc ∑ κ, revWt X Z M (B κ) (.inr T) σ
          ≤ ∑ κ, ∑ s ∈ T ∩ J, (if s ∈ B κ then ENNReal.ofReal σ.trace.re else 0) :=
            Finset.sum_le_sum fun κ _ ↦ hstep κ
        _ = ∑ s ∈ T ∩ J, ((Finset.univ.filter fun κ ↦ s ∈ B κ).card : ℝ≥0∞) *
              ENNReal.ofReal σ.trace.re := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ T ∩ J, ε * Fintype.card K * ENNReal.ofReal σ.trace.re :=
            Finset.sum_le_sum fun s hs ↦
              mul_le_mul_of_nonneg_right (hε s (Finset.mem_inter.mp hs).2) zero_le
        _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp only [candCharge]
            ring
  calc ∑ κ, revW m₀ I (B κ) x ρ
      = (runtimeR m₀).totalWeight I (fun i σ ↦ ∑ κ, revWt X Z M (B κ) i σ) x ρ :=
        (totalWeight_fintype_sum (runtimeR m₀) I (fun κ ↦ revWt X Z M (B κ)) x ρ).symm
    _ ≤ (runtimeR m₀).totalWeight I (fun i σ ↦ ((Fintype.card K : ℝ≥0∞) * ε) *
          ((candCharge X Z M J i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) x ρ :=
        totalWeight_le_totalWeight _ I (fun i σ _ ↦ hpoint i σ) x hρ
    _ = ((Fintype.card K : ℝ≥0∞) * ε) * (runtimeR m₀).totalWeight I (fun i σ ↦
          (candCharge X Z M J i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) x ρ :=
        totalWeight_const_mul_weight (runtimeR m₀) I ((Fintype.card K : ℝ≥0∞) * ε)
          (fun i σ ↦ (candCharge X Z M J i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) x ρ
    _ ≤ ((Fintype.card K : ℝ≥0∞) * ε) * (R * ENNReal.ofReal ρ.trace.re) :=
        mul_le_mul_of_nonneg_left
          (totalWeight_chargeTrace_le (runtimeR m₀) I (candCharge X Z M J) x hR hρ) zero_le
    _ = _ := by ring

/-- **The record mass averaged over a coordinate the run ignores** is at most `R · ε` times the
trace (`sum_revW_le`). -/
theorem uavg_revW_le (m₀ : Finset S × M) (I : L.Interp) {A : QReg}
    (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ} (hρ : ρ.PosSemidef) {K : Type*} [Fintype K] (B : K → Finset S) (J : Finset S)
    (hBJ : ∀ κ, B κ ⊆ J) (ε : ℝ≥0∞)
    (hε : ∀ s ∈ J, ((Finset.univ.filter fun κ ↦ s ∈ B κ).card : ℝ≥0∞) ≤ ε * Fintype.card K)
    {R : ℕ} (hR : IFreeM.IsChargeBound x (portCharge (candCharge X Z M J)) R) :
    uavg (fun κ ↦ revW m₀ I (B κ) x ρ) ≤ R * ε * ENNReal.ofReal ρ.trace.re := by
  unfold uavg
  by_cases hK : (Fintype.card K : ℝ≥0∞) = 0
  · have : IsEmpty K := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hK)
    simp [Finset.univ_eq_empty]
  · calc (Fintype.card K : ℝ≥0∞)⁻¹ * ∑ κ, revW m₀ I (B κ) x ρ
        ≤ (Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card K * (R * ε * ENNReal.ofReal ρ.trace.re)) :=
          mul_le_mul_of_nonneg_left (sum_revW_le m₀ I x hρ B J hBJ ε hε hR) zero_le
      _ = _ := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hK (ENNReal.natCast_ne_top _), one_mul]

end avg

end Quantum.Xmss.Hybrid

end
