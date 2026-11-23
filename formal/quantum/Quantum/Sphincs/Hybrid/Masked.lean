module

public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.Xmss.Hybrid.GradedMasked
public import Quantum.Sphincs.Assembly.GoodES
public import Quantum.Sphincs.Assembly.MassSources
public import Quantum.Sphincs.Assembly.ChgRev

@[expose] public section

/-!
# leanSPHINCS's masked graded hybrid and the bridge to the event side

* **The win probability under a mismatch** (`evalDistMap_winBit_le_mismatch`): Mismatch's
  `totalWeight_le_mismatch` for the final win bit. For a template that reveals before it programs
  and keeps the label, run from `initU m₀` with `m₀.1` disjoint from `B`, the win probabilities at
  hidden values `v`, `v'` agreeing off `B` satisfy `P(v) ≤ P(v') + R(v')`, with `R` the
  first-meeting record mass (the inputs, labelled off `B`, of the record calls meeting `B`:
  Mismatch's `revSet`, ChgRev's `revFirst`). The final branch is lazy (GradedMasked's
  `lazy_run_realizeT`), so its mass on labels avoiding `B` is the same at `v` and `v'`; its mass on
  labels meeting `B` (`finMeetW`) is at most `R(v)` (`finMeetW_le_revSet`: labels change only at
  records, so a final label meeting `B` passed a record meeting `B` from a label avoiding it), and
  `R(v) = R(v')` (the view off `B`).
* **The masked graded hybrid** (`uavg_p1R_le`): GradedMasked's
  `uavg_win_runtime1R_le_graded_total_masked` over the padded tables `FT`, runtime 1 with
  `fullHw (tabOf t)` against runtime 2 on `gameR msgPol`, the sponge and read masses masked by
  ReparamFull's `FullG S` (hypotheses `hS`, `hRd`, the cover sets `hcov`), the bad fraction
  `stageFrac S` (`≤ 2^-197 + 2^-400 + static`, `stageFrac_le_keccak`) paid once.
* **From the tables to the template data** (`uavg_p2R_tab_le`): on `FullG S` the game at the table
  is the game at `fullE`'s data up to the charged coordinates (`hgame_fullE`, ChgRev's `chgBK`), so
  the win is at most the win at the data plus `winChg` (ChgRev's `revFirst`, `p2R_tab_le_winChg`);
  `fullE` is injective there (`uavg_mask_le_uavg_of_injOn`), so the table average is at most the
  average over `PP × V` plus `winChgAvg A S` plus `stageFrac S`. `uavg_pubP_eq_full`: that
  average is the event side's over `FullES` (the slot bits `PubR` padding).
* **The chain** (`uavg_p2R_msgPol_full_le`, `winProb_le_masked`): EventSide's
  `uavg_p2R_msgPol_le_es'` at every `(PK.seed, π, h)` with `PermGood π 18`, GoodES's
  `uavg_not_goodES_le` and `2^-777` for the bad permutations.
-/

open Matrix MeasureTheory IPFunctor
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Sphincs.Hybrid

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly
open Quantum.Xmss.Hybrid (diagMass setProj diagMass_eq_ofReal_trace_conj diagMass_le diagMass_mono
  diagMass_empty diagMass_eq_inter_add_diff diagMass_eq_of_querySupportedOn revSet revWt revW
  recMeets KeepsLab ReadKeeps StepLab stepLab_sponge stepLab_read stepLab_prog stepLab_rec Agree
  Lazy lazy_const suppAt_empty queryWeight_eq_of_viewBy_off totalWeight_le_totalWeight restrictTo
  querySupportedOn_initR querySupportedOn_queryStep)

/-! ## Diagonal masses of sequenced branches -/

section bind

/-- **The diagonal mass of a branch of a sequence** is the sum over the first outcomes of the
diagonal masses of the continuations' branches. -/
theorem diagMass_bind_branch {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] {C : κ → Type} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) (T : Set (C c))
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    diagMass T ((p.bind k).branch c ρ) = ∑' i, diagMass T ((k i).branch c (p.branch i ρ)) := by
  rw [diagMass_eq_ofReal_trace_conj T ((p.bind k).posSemidef_branch_apply c hρ),
    ofReal_trace_conj_bind_branch p k c (setProj T) hρ]
  exact tsum_congr fun i ↦ (diagMass_eq_ofReal_trace_conj T
    ((k i).posSemidef_branch_apply c (p.posSemidef_branch_apply i hρ))).symm

/-- The trace weight of a positive semidefinite operator is the diagonal mass of all states. -/
theorem ofReal_trace_eq_diagMass {α Λ : Type} [Fintype α] [DecidableEq α] (g : α → Λ)
    {σ : Matrix α α ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal σ.trace.re = diagMass {p | g p ∈ (Set.univ : Set Λ)} σ :=
  (diagMass_eq_of_querySupportedOn (g := g) (T := Set.univ) hσ fun _ _ _ ↦
    ⟨Set.mem_univ _, Set.mem_univ _⟩).symm

end bind

/-! ## The final mass on labels meeting a set -/

section meet

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The final mass on labels meeting `B`**: the diagonal mass, summed over the leaves of the run,
of the register states whose memory label meets `B`. -/
noncomputable def finMeetW (m₀ : Finset S × M) (I : L.Interp) (B : Finset S) {A : QReg}
    (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) : ℝ≥0∞ :=
  ∑' p : Σ u, Ω u, diagMass {q : p.1 × QReg.of (HwReg X Z (Finset S × M)) |
    ¬Disjoint q.2.2.2.1 B} (((runtimeR m₀).run I x).branch p ρ)

variable (m₀ : Finset S × M) (I : L.Interp) (B : Finset S)

theorem finMeetW_primBind {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (recHwSpec X Z S M) Ω (L.next o b))
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ} (hρ : ρ.PosSemidef) :
    finMeetW m₀ I B (QuantumComp.primBind o k) ρ =
      ∑' b, finMeetW m₀ I B (k b) (((I o).frame (runtimeR (X := X) (Z := Z) m₀).D).branch b ρ) := by
  unfold finMeetW
  simp only [QuantumRuntime.run_primBind]
  rw [← ENNReal.tsum_comm]
  exact tsum_congr fun p ↦ diagMass_bind_branch
    (C := fun p : Σ u, Ω u ↦ p.1 × QReg.of (HwReg X Z (Finset S × M))) _ _ p _ hρ

theorem finMeetW_queryBind {A : QReg} (i : (recHwSpec X Z S M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    (k : (recHwSpec X Z S M).Result i →
      QuantumComp L (recHwSpec X Z S M) Ω (QReg.of ((recHwSpec X Z S M).Out i × E)))
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ} (hρ : ρ.PosSemidef) :
    finMeetW m₀ I B (QuantumComp.queryBind i E ℓ k) ρ =
      ∑' r, finMeetW m₀ I B (k r) (((runtimeR m₀).queryStep i E ℓ).branch r ρ) := by
  unfold finMeetW
  simp only [QuantumRuntime.run_queryBind]
  rw [← ENNReal.tsum_comm]
  exact tsum_congr fun p ↦ diagMass_bind_branch
    (C := fun p : Σ u, Ω u ↦ p.1 × QReg.of (HwReg X Z (Finset S × M))) _ _ p _ hρ

/-- The final mass on labels meeting `B` is at most the trace. -/
theorem finMeetW_le_trace {A : QReg} (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ} (hρ : ρ.PosSemidef) :
    finMeetW m₀ I B x ρ ≤ ENNReal.ofReal ρ.trace.re :=
  (ENNReal.tsum_le_tsum fun p ↦ diagMass_le _ (((runtimeR m₀).run I x).posSemidef_branch_apply p
    hρ)).trans (((runtimeR m₀).run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)

omit [Fintype S] [DecidableEq S] in
/-- On one label avoiding `B`, the states meeting `B` weigh nothing. -/
theorem diagMass_meet_eq_zero {α : Type} [Fintype α] (lab : α → Finset S) {t : Finset S}
    (ht : Disjoint t B) {σ : Matrix α α ℂ} (hσ : QuerySupportedOn lab {t} σ) :
    diagMass {q | ¬Disjoint (lab q) B} σ = 0 := by
  refine le_antisymm ((Xmss.Assembly.diagMass_mono_supp (S' := ∅) fun a ha hm ↦ ?_).trans_eq
    (diagMass_empty σ)) zero_le
  have hl : lab a = t := Set.mem_singleton_iff.mp (hσ a a ha).1
  exact absurd (hl ▸ ht) hm

/-- One call that keeps the label off `B`. -/
theorem finMeetW_queryBind_le {A : QReg} (i : (recHwSpec X Z S M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    (k : (recHwSpec X Z S M).Result i →
      QuantumComp L (recHwSpec X Z S M) Ω (QReg.of ((recHwSpec X Z S M).Out i × E)))
    {t t' : Finset S} (hstep : StepLab m₀ i t t')
    (hk : ∀ r (ρ' : Matrix (QReg.of ((recHwSpec X Z S M).Out i × E) ×
        QReg.of (HwReg X Z (Finset S × M)))
        (QReg.of ((recHwSpec X Z S M).Out i × E) × QReg.of (HwReg X Z (Finset S × M))) ℂ),
      ρ'.PosSemidef →
      QuerySupportedOn (fun p : QReg.of ((recHwSpec X Z S M).Out i × E) ×
        QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t'} ρ' →
      finMeetW m₀ I B (k r) ρ' ≤
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i)) (k r) ρ')
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t} ρ) :
    finMeetW m₀ I B (QuantumComp.queryBind i E ℓ k) ρ ≤
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
        (QuantumComp.queryBind i E ℓ k) ρ := by
  rw [finMeetW_queryBind m₀ I B i E ℓ k hρ, (runtimeR m₀).totalWeight_queryBind I i E ℓ k ρ]
  exact (ENNReal.tsum_le_tsum fun r ↦ hk r _
    (((runtimeR m₀).queryStep i E ℓ).posSemidef_branch_apply r hρ)
    (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s.2.2.1) i r (hstep r) E ℓ hs)).trans
    le_add_self

/-- One record call meeting `B`: the rest of the run is paid by its trace. -/
theorem finMeetW_queryBind_rec_le {A : QReg} (T : Finset S) (hT : ¬Disjoint T B) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In (.inr T) × E)
    (k : (recHwSpec X Z S M).Result (.inr T) →
      QuantumComp L (recHwSpec X Z S M) Ω (QReg.of ((recHwSpec X Z S M).Out (.inr T) × E)))
    {t : Finset S} (ht : Disjoint t B)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M)))
      ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) {t} ρ) :
    finMeetW m₀ I B (QuantumComp.queryBind (.inr T) E ℓ k) ρ ≤
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i))
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
  rw [finMeetW_queryBind m₀ I B _ E ℓ k hρ, (runtimeR m₀).totalWeight_queryBind I _ E ℓ k ρ]
  calc ∑' r, finMeetW m₀ I B (k r) (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ)
      ≤ ∑' r, ENNReal.ofReal (((runtimeR m₀).queryStep (.inr T) E ℓ).branch r ρ).trace.re :=
        ENNReal.tsum_le_tsum fun r ↦ finMeetW_le_trace m₀ I B (k r)
          (((runtimeR m₀).queryStep (.inr T) E ℓ).posSemidef_branch_apply r hρ)
    _ ≤ ENNReal.ofReal ρ.trace.re :=
        ((runtimeR m₀).queryStep (.inr T) E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    _ = diagMass (revSet X Z M B (.inr T)) (callInput ℓ (runtimeR m₀).D ρ) := hrev.symm
    _ ≤ _ := le_self_add

variable {S' : Type} [Fintype S'] [DecidableEq S'] {D : S' → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {good : Xmss.Hybrid.LazyProg X Z S' D → Prop}

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- **Final labels meeting `B` come from records.** From states on one memory label avoiding `B`,
the final mass on labels meeting `B` is at most the mass, labelled off `B`, of the record calls
meeting `B`. -/
theorem finMeetW_le_revSet (m₀ : Finset S' × M) (I : L.Interp) (B : Finset S')
    (v : (s : S') → D s) {A : QReg} (y : QuantumComp L (tmplSpec X Z S' D M good) Ω A)
    (hy : KeepsLab y) :
    ∀ (t : Finset S'), Disjoint t B →
      ∀ ρ : Matrix (A × QReg.of (HwReg X Z (Finset S' × M)))
        (A × QReg.of (HwReg X Z (Finset S' × M))) ℂ, ρ.PosSemidef →
      QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset S' × M)) ↦ p.2.2.2.1) {t} ρ →
      finMeetW m₀ I B (realizeT v y) ρ ≤
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z M B i)) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    intro t ht ρ _ hs
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun p ↦ ?_) zero_le
    show diagMass _ (((runtimeR m₀).run I (QuantumComp.pure y)).branch p ρ) = 0
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact diagMass_meet_eq_zero B (fun q : _ × QReg.of (HwReg X Z (Finset S' × M)) ↦ q.2.2.2.1)
        ht hs
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact Xmss.Assembly.diagMass_zero _
  | primBind _ o k ih =>
    intro t ht ρ hρ hs
    refine (finMeetW_primBind m₀ I B o (fun b ↦ realizeT v (k b)) hρ).trans_le
      (le_of_le_of_eq (ENNReal.tsum_le_tsum fun b ↦ ih b (hy.2 (ULift.up b)) t ht _
        (((I o).frame _).posSemidef_branch_apply b hρ)
        (QuerySupportedOn.amplify_snd (q := fun s : HwReg X Z (Finset S' × M) ↦ s.2.2.1) hs _))
      ((runtimeR m₀).totalWeight_primBind I o (fun b ↦ realizeT v (k b)) ρ).symm)
  | queryBind A' i E ℓ k ih =>
    intro t ht ρ hρ hs
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact finMeetW_queryBind_le m₀ I B (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (stepLab_sponge m₀ i t)
        (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) t ht ρ' hρ' hs') ρ hρ hs
    · exact finMeetW_queryBind_le m₀ I B (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (stepLab_read m₀ c.1 hy.1 t)
        (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) t ht ρ' hρ' hs') ρ hρ hs
    · cases p with
      | programH T₀ c =>
        exact finMeetW_queryBind_le m₀ I B
          (.inl (.inr ((Xmss.Hybrid.LazyProg.programH T₀ c).realize v))) E ℓ
          (fun r ↦ realizeT v (k r)) (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) t ht ρ' hρ' hs') ρ hρ hs
      | programK T₀ c =>
        exact finMeetW_queryBind_le m₀ I B
          (.inl (.inr ((Xmss.Hybrid.LazyProg.programK T₀ c).realize v))) E ℓ
          (fun r ↦ realizeT v (k r)) (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) t ht ρ' hρ' hs') ρ hρ hs
      | programK' T₀ c =>
        exact finMeetW_queryBind_le m₀ I B
          (.inl (.inr ((Xmss.Hybrid.LazyProg.programK' T₀ c).realize v))) E ℓ
          (fun r ↦ realizeT v (k r)) (stepLab_prog m₀ _ t)
          (fun r ρ' hρ' hs' ↦ ih r (hy.2 (ULift.up r)) t ht ρ' hρ' hs') ρ hρ hs
    · by_cases hTB : Disjoint T B
      · exact finMeetW_queryBind_le m₀ I B (.inr T) E ℓ
          (fun m ↦ realizeT v (k (restrictTo T v, m))) (stepLab_rec m₀ T t)
          (fun r ρ' hρ' hs' ↦ ih (restrictTo T v, r) (hy.2 (ULift.up (restrictTo T v, r)))
            (t ∪ T) (Finset.disjoint_union_left.mpr ⟨ht, hTB⟩) ρ' hρ' hs') ρ hρ hs
      · exact finMeetW_queryBind_rec_le m₀ I B T hTB E ℓ
          (fun m ↦ realizeT v (k (restrictTo T v, m))) ht ρ hρ hs

end meet

/-! ## The win probability under a mismatch -/

section win

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  {good : Xmss.Hybrid.LazyProg X Z S D → Prop}

/-- **The win probability under a mismatch.** Let the template `y` reveal before it programs and
keep the label, and let the hidden values `v`, `v'` agree off `B`, with the initial label `m₀.1`
disjoint from `B`. Then the win probability at `v` is at most that at `v'` plus the first-meeting
record mass of `B` at `v'` (the inputs, labelled off `B`, of the record calls meeting `B`). -/
theorem evalDistMap_winBit_le_mismatch (m₀ : Finset S × M)
    (y : QComp (tmplSpec X Z S D M good) (QReg.of Unit) (QReg.of Unit) Bool)
    (hdisc : Xmss.Assembly.Disc y ∅) (hy : KeepsLab y) (B : Finset S) (hB : Disjoint m₀.1 B)
    {v v' : (s : S) → D s} (hv : Agree (Finset.univ \ B) v v') :
    (runtimeR m₀).evalDistMap .instruments (realizeT v y) (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).evalDistMap .instruments (realizeT v' y) (SubState.basis ()) winBit {true} +
        (runtimeR m₀).totalWeight .instruments (fun i ↦ diagMass (revSet X Z M B i))
          (realizeT v' y) (initU m₀) := by
  set lab : QReg.of Unit × QReg.of (HwReg X Z (Finset S × M)) → Finset S := fun q ↦ q.2.2.2.1
  set P : Set (QReg.of Unit × QReg.of (HwReg X Z (Finset S × M))) := {q | Disjoint (lab q) B}
  set U : Set (QReg.of Unit × QReg.of (HwReg X Z (Finset S × M))) :=
    {q | lab q ∈ (Set.univ : Set (Finset S))}
  have hpos : ∀ u : (s : S) → D s,
      (((runtimeR m₀).run₂ .instruments (realizeT u y)).branch true (initU m₀)).PosSemidef :=
    fun u ↦ ((runtimeR m₀).run₂ .instruments (realizeT u y)).posSemidef_branch_apply true
      (initU_posSemidef m₀)
  have hL := lazy_run_realizeT (I := LocalSig.Interp.instruments) m₀ y ∅ hdisc
    (fun _ ↦ initU m₀) (lazy_const _ _) (fun _ ↦ suppAt_empty _ _)
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true)
  have hagree : ∀ a ∈ P, ((runtimeR m₀).run₂ .instruments (realizeT v y)).branch true
      (initU m₀) a a = ((runtimeR m₀).run₂ .instruments (realizeT v' y)).branch true
      (initU m₀) a a := fun a ha ↦
    hL a a v v' (hv.mono fun s hs ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ s,
      Finset.disjoint_left.mp ha ((Finset.mem_union.mp hs).elim id id : s ∈ lab a)⟩)
  have hgood : diagMass (U ∩ P) (((runtimeR m₀).run₂ .instruments (realizeT v y)).branch true
      (initU m₀)) = diagMass (U ∩ P) (((runtimeR m₀).run₂ .instruments (realizeT v' y)).branch
      true (initU m₀)) := by
    unfold diagMass
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases ha : a ∈ U ∩ P
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hagree a ha.2]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]
  have hmeet : diagMass (U \ P) (((runtimeR m₀).run₂ .instruments (realizeT v y)).branch true
      (initU m₀)) ≤ finMeetW m₀ .instruments B (realizeT v y) (initU m₀) := by
    refine (diagMass_mono (T := {q : QReg.of Unit × QReg.of (HwReg X Z (Finset S × M)) |
      ¬Disjoint q.2.2.2.1 B}) (fun q hq ↦ hq.2) _).trans ?_
    unfold finMeetW
    exact ENNReal.le_tsum (f := fun p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u ↦
      diagMass {q : p.1 × QReg.of (HwReg X Z (Finset S × M)) | ¬Disjoint q.2.2.2.1 B}
        (((runtimeR m₀).run .instruments (realizeT v y)).branch p (initU m₀)))
      (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true)
  have hrevSet : ∀ i p, p ∈ revSet X Z M B i → Disjoint p.2.2.2.1 B := fun i p hp ↦ by
    unfold revSet at hp
    split_ifs at hp
    · exact hp
    · exact hp.elim
  have hview : (runtimeR m₀).totalWeight .instruments (fun i ↦ diagMass (revSet X Z M B i))
      (realizeT v y) (initU m₀) = (runtimeR m₀).totalWeight .instruments
        (fun i ↦ diagMass (revSet X Z M B i)) (realizeT v' y) (initU m₀) :=
    tsum_congr fun j ↦ queryWeight_eq_of_viewBy_off (runtimeR m₀) .instruments
      (fun r ↦ r.2.2.1) (fun u ↦ realizeT u y) (fun _ ↦ initU m₀) j
      (viewBy_runtimeR_of_disc .instruments m₀ y ∅ hdisc (fun _ ↦ initU m₀) (lazy_const _ _)
        (fun _ ↦ suppAt_empty _ _) j) B hv (revSet X Z M B) hrevSet
  have hfin := finMeetW_le_revSet m₀ .instruments B v y hy m₀.1 hB (initU m₀)
    (initU_posSemidef m₀) (by unfold initU; exact querySupportedOn_initR m₀ _)
  refine (evalDistMap_winBit m₀ (realizeT v y)).trans_le (le_of_le_of_eq ?_
    (congrArg (· + (runtimeR m₀).totalWeight .instruments (fun i ↦ diagMass (revSet X Z M B i))
      (realizeT v' y) (initU m₀))
      (evalDistMap_winBit m₀ (realizeT v' y)).symm))
  exact ((ofReal_trace_eq_diagMass lab (hpos v)).trans ((diagMass_eq_inter_add_diff U P _).trans
    (congrArg (· + _) hgood))).trans_le ((add_le_add (diagMass_mono Set.inter_subset_left _)
      (hmeet.trans (hfin.trans hview.le))).trans_eq
      (congrArg (· + _) (ofReal_trace_eq_diagMass lab (hpos v')).symm))

end win

/-! ## Averages through an injection and over padded products -/

section avg

open Quantum.Xmss.Hybrid (uavg)

/-- **A masked average through an injection on a good set** is at most the average over the
public data and the hidden values: `e` maps `Θ` into `P × (V × K)`, injectively on `G`, with
`|P| |V × K| ≤ |Θ|`; a function of `(p, v)` averaged over `G` (`0` off `G`) is at most its
average over `P × V`. -/
theorem uavg_mask_le_uavg_of_injOn {Θ P V K : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    [Fintype K] [Nonempty K] (e : Θ → P × (V × K)) (G : Θ → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t}) (iVK : Fintype (V × K))
    (hcard : Fintype.card P * @Fintype.card (V × K) iVK ≤ Fintype.card Θ)
    (g : P × V → ℝ≥0∞) :
    uavg (fun t ↦ if G t then g ((e t).1, (e t).2.1) else 0) ≤ uavg g := by
  classical
  obtain rfl := Subsingleton.elim iVK (instFintypeProd V K)
  rw [Fintype.card_prod] at hcard
  have hK0 : (Fintype.card K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : ∑ t ∈ Finset.univ.filter G, g ((e t).1, (e t).2.1) ≤
      (Fintype.card K : ℝ≥0∞) * ∑ y : P × V, g y := by
    have himg : ∑ t ∈ Finset.univ.filter G, g ((e t).1, (e t).2.1) =
        ∑ y ∈ (Finset.univ.filter G).image e, g (y.1, y.2.1) :=
      (Finset.sum_image (f := fun y : P × (V × K) ↦ g (y.1, y.2.1)) fun a ha b hb h ↦
        hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h).symm
    rw [himg]
    refine (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans_eq ?_
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mul_sum]
  have hle : (Fintype.card Θ : ℝ≥0∞)⁻¹ ≤
      ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)))]
    refine ENNReal.inv_le_inv.mpr ?_
    rw [mul_assoc]
    exact_mod_cast hcard
  unfold uavg
  rw [← Finset.sum_filter, Fintype.card_prod, Nat.cast_mul]
  calc (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ t ∈ Finset.univ.filter G, g ((e t).1, (e t).2.1)
      ≤ ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹ *
          ((Fintype.card K : ℝ≥0∞) * ∑ y : P × V, g y) := mul_le_mul' hle hsum
    _ = ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ *
          (((Fintype.card K : ℝ≥0∞)⁻¹ * Fintype.card K) * ∑ y : P × V, g y) := by
        rw [mul_assoc, mul_assoc]
    _ = _ := by rw [ENNReal.inv_mul_cancel hK0 (ENNReal.natCast_ne_top _), one_mul]

/-- **Averaging over a padded middle coordinate**: a function not depending on `R` averages over
`((H × W) × R) × V` (with any instance on `(H × W) × R`) as over `(H × W) × V`. -/
theorem uavg_pad_mid {H W R V : Type*} [Fintype H] [Fintype W] [Fintype R] [Nonempty R]
    [Fintype V] (iHWR : Fintype ((H × W) × R)) (F : H → W → V → ℝ≥0∞) :
    @uavg (((H × W) × R) × V) (@instFintypeProd _ _ iHWR _) (fun y ↦ F y.1.1.1 y.1.1.2 y.2) =
      uavg (fun y : (H × W) × V ↦ F y.1.1 y.1.2 y.2) := by
  obtain rfl := Subsingleton.elim iHWR (instFintypeProd (H × W) R)
  rw [Assembly.uavg_prod_iter,
    Assembly.uavg_prod_iter (fun y : (H × W) × V ↦ F y.1.1 y.1.2 y.2)]
  exact Assembly.uavg_fst_marg (fun x : H × W ↦ uavg fun v ↦ F x.1 x.2 v)

/-- An average of values at most `1` is at most `1`. -/
theorem uavg_le_one_of_le {Θ : Type*} [Fintype Θ] {f : Θ → ℝ≥0∞} (h : ∀ θ, f θ ≤ 1) :
    uavg f ≤ 1 :=
  (Xmss.Hybrid.uavg_mono h).trans (Xmss.Assembly.uavg_const_le 1)

end avg

end Quantum.Sphincs.Hybrid

/-! ## leanSPHINCS's masked graded hybrid -/

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common Common.SufCma
open HashSig (PublicParameter)
open Quantum.SufCma
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul uavg_ite_zero_one Covers spongeMass
  readMass evalDistMap_apply_le_one uavg_win_runtime1R_le_graded_total_masked diagMass revSet Agree)
open Quantum.Xmss.Assembly (runtimeR runtime1R realizeT uavg_const uavg_const_le XW
  permTerm_le_keccak winBit initU)
open Quantum.Sphincs.Hybrid (evalDistMap_winBit_le_mismatch uavg_mask_le_uavg_of_injOn
  uavg_pad_mid uavg_le_one_of_le)

namespace Quantum.Sphincs.Assembly

/-- **The target of the masked graded hybrid** (leanXMSS's `hybTerm`): `√(4 · 6q · μ) + √ν` with
the sponge-port mass `μ = 6q κ` over at most `6q` sponge calls and the read-port mass `ν`. -/
noncomputable def hybTermS (q : ℕ) (κ ν : ℝ≥0∞) : ℝ≥0∞ :=
  (4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * κ))) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)

open scoped Classical in
/-- **The stage fraction**: the padded tables off ReparamFull's good set `FullG S`, paid once
(at most `2^-197 + 2^-400` plus the static condition's fraction, `fullG_frac_le_keccak`). -/
noncomputable def stageFrac (S : PP → ((s : HPos) → XD s) → Prop) : ℝ≥0∞ :=
  (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullG S t).card

open scoped Classical in
theorem stageFrac_le_keccak (S : PP → ((s : HPos) → XD s) → Prop) :
    stageFrac S ≤ ENNReal.ofReal (1 / 2 ^ 197) + ENNReal.ofReal (1 / 2 ^ 400) +
      (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card :=
  fullG_frac_le_keccak S

section hybrid

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
/-- **leanSPHINCS's masked graded hybrid** (leanXMSS's `uavg_p1R_le`): runtime 1 with the full table
against runtime 2 on the canonical game at `msgPol`, averaged over the padded tables, the masses
masked by ReparamFull's good set `FullG S` (`hS`: at most `6q κ` at the sponge ports, `hRd`: at
most `ν` at the read ports; the cover sets `Hh`, `Hk`, `Hk'` of the full table, `hcov`), the bad
fraction `stageFrac S` paid once. -/
theorem uavg_p1R_le (S : PP → ((s : HPos) → XD s) → Prop) (Hh : FT → Set Z) (Hk Hk' : FT → Set X)
    (hcov : ∀ t, Covers (fullHw (tabOf t)) (Hh t) (Hk t) (Hk' t)) (κ ν : ℝ≥0∞)
    (hS : uavg (fun t : FT ↦ if FullG S t then (runtimeR m0R).totalWeight .instruments
      (spongeMass (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)))
        initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * κ)
    (hRd : uavg (fun t : FT ↦ if FullG S t then (runtimeR m0R).totalWeight .instruments
      (readMass (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)))
        initR else 0) ≤ ν) :
    uavg (p1R A fullHw) ≤
      (uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) ^ (2⁻¹ : ℝ) + hybTermS q κ ν) ^ 2 +
        stageFrac S := by
  have h := uavg_win_runtime1R_le_graded_total_masked .instruments
    (fun t : FT ↦ fullHw (tabOf t)) Hh Hk Hk' hcov m0R
    (fun t ↦ gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObs) (measurableSet_singleton true) (6 * q)
    (fun t ↦ advCalls_gameR hperm hsign msgPol _ _) (FullG S) _ ν hS hRd
  have e1 : uavg (fun t : FT ↦ p1R A fullHw (tabOf t)) = uavg (p1R A fullHw) :=
    uavg_tabOf (p1R A fullHw)
  have e2 : uavg (fun t : FT ↦ p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) =
      uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) :=
    uavg_tabOf (fun L ↦ p2R msgPol A (pubOf L) (valueAt L))
  refine (e1.symm.trans_le h).trans_eq ?_
  unfold hybTermS stageFrac
  rw [← e2, add_assoc]
  rfl

end hybrid

/-! ## From the tables to the template data -/

section bridge

variable (A : SAdversary)

/-- Win probabilities are at most `1`. -/
theorem p2R_le_one (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    p2R pol A p v ≤ 1 :=
  QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _

/-- The initial state of the runtimes with record ports is WinDecomp's. -/
theorem initR_eq_initU : initR = initU (X := X) (Z := Z) m0R := by
  unfold initR initU
  rfl

/-- **The charged first-meeting record mass of the win** at a padded table: ChgRev's `revFirst` of
the charged coordinates `chgBK (fullE t)` in the canonical game at `fullE`'s data, from `initR`. -/
noncomputable def winChg (t : FT) : ℝ≥0∞ :=
  revFirst m0R LocalSig.Interp.instruments (chgBK (fullE t))
    (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) initR

open scoped Classical in
/-- **The win's mismatch term**: `winChg` averaged over the padded tables of the good set
`FullG S` (`0` elsewhere). -/
noncomputable def winChgAvg (S : PP → ((s : HPos) → XD s) → Prop) : ℝ≥0∞ :=
  uavg fun t : FT ↦ if FullG S t then winChg A t else 0

/-- **The win at a good table is the win at the reparametrized data plus the charged first-meeting
record mass** (`hgame_fullE`, ChgRev's `chgB_subset_chgBK`, `evalDistMap_winBit_le_mismatch` with
`B = chgBK (fullE t)`). -/
theorem p2R_tab_le_winChg {t : FT} (ht : FullGCore t) :
    p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) ≤
      p2R msgPol A (pubP (fullE t).1) (fullE t).2.1 + winChg A t := by
  obtain ⟨v, hv, hgeq⟩ := hgame_fullE A ht
  have hv' : Agree (Finset.univ \ chgBK (fullE t)) v (fullE t).2.1 :=
    hv.mono (Finset.sdiff_subset_sdiff le_rfl (chgB_subset_chgBK (fullD_of_core ht)))
  have hB : Disjoint m0R.1 (chgBK (fullE t)) := Finset.disjoint_empty_left _
  have h := evalDistMap_winBit_le_mismatch m0R
    (gameT Selections cwUpd msgPol (pubP (fullE t).1) A)
    (disc_gameT Selections cwUpd msgPol _ A ∅) (keepsLab_gameT Selections cwUpd msgPol _ A)
    (chgBK (fullE t)) hB hv'
  have e1 : p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) =
      p2R msgPol A (pubP (fullE t).1) v :=
    congrArg (fun x ↦ (runtimeR m0R).evalDistMap .instruments x (SubState.basis ()) winObs
      {true}) hgeq
  have e2 : p2R msgPol A (pubP (fullE t).1) (fullE t).2.1 =
      (runtimeR m0R).evalDistMap .instruments
        (realizeT (fullE t).2.1 (gameT Selections cwUpd msgPol (pubP (fullE t).1) A))
        (SubState.basis ()) winBit {true} := rfl
  have e3 : winChg A t = (runtimeR m0R).totalWeight .instruments
      (fun i ↦ diagMass (revSet X Z Selections (chgBK (fullE t)) i))
      (realizeT (fullE t).2.1 (gameT Selections cwUpd msgPol (pubP (fullE t).1) A))
      (initU m0R) := by
    unfold winChg
    rw [initR_eq_initU]
    rfl
  exact e1.trans_le (h.trans_eq (congrArg₂ (· + ·) e2.symm e3.symm))

open scoped Classical in
/-- **The table average of the win at `msgPol` through the reparametrization**: at most the
average over the template data `(p, v)`, the win's mismatch term `winChgAvg A S` and the stage
fraction `stageFrac S` of the good set `FullG S`. -/
theorem uavg_p2R_tab_le (S : PP → ((s : HPos) → XD s) → Prop) :
    uavg (fun L ↦ p2R msgPol A (pubOf L) (valueAt L)) ≤
      uavg (fun y : PP × ((s : HPos) → XD s) ↦ p2R msgPol A (pubP y.1) y.2) +
        winChgAvg A S + stageFrac S := by
  rw [← uavg_tabOf (fun L ↦ p2R msgPol A (pubOf L) (valueAt L))]
  have hpt : ∀ t : FT, p2R msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) ≤
      ((if FullG S t then p2R msgPol A (pubP (fullE t).1) (fullE t).2.1 else 0) +
        (if FullG S t then winChg A t else 0)) + (if FullG S t then 0 else 1) := fun t ↦ by
    by_cases hg : FullG S t
    · simp only [hg, ↓reduceIte, add_zero]
      exact p2R_tab_le_winChg A hg.1
    · simp only [hg, ↓reduceIte, zero_add]
      exact p2R_le_one A msgPol _ _
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add]
  exact add_le_add (add_le_add (uavg_mask_le_uavg_of_injOn fullE (FullG S)
    (fullE_spec S A).1 _ card_coords.le (fun y ↦ p2R msgPol A (pubP y.1) y.2)) le_rfl)
    (uavg_ite_zero_one (FullG S)).le

/-- The template data as `(PK.seed, π, h)` and the event side's `((k, k'), v)`. -/
def esEquiv : ((Z → X) × XW) × ((s : HPos) → XD s) ≃ FullES where
  toFun y := ((y.1.2.1, y.1.2.2.1, y.1.1), ((y.1.2.2.2.1, y.1.2.2.2.2), y.2))
  invFun ω := ((ω.1.2.2, (ω.1.1, ω.1.2.1, ω.2.1.1, ω.2.1.2)), ω.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The average over the template data is the event side's**: over `FullES` (`(PK.seed, π, h)`,
then the keys `(k, k')` and the hidden values `v`), the slot bits `PubR` padding. -/
theorem uavg_pubP_eq_full :
    uavg (fun y : PP × ((s : HPos) → XD s) ↦ p2R msgPol A (pubP y.1) y.2) =
      uavg (fun ω : FullES ↦ p2R msgPol A (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2) :=
  (uavg_pad_mid instFintypePP fun (h : Z → X) (w : XW) v ↦ p2R msgPol A (sPub w h) v).trans
    (uavg_comp_equiv esEquiv fun ω : FullES ↦
      p2R msgPol A (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2)

/-- The permutations that are not `PermGood π 18`, among `(PK.seed, π, h)`: at most `2^-777`. -/
theorem uavg_not_permGood_es :
    uavg (fun a : PublicParameter × Equiv.Perm (X × Z) × (Z → X) ↦
      if PermGood a.2.1 18 then (0 : ℝ≥0∞) else 1) ≤ ENNReal.ofReal (1 / 2 ^ 777) := by
  rw [Assembly.uavg_snd_marg (fun b : Equiv.Perm (X × Z) × (Z → X) ↦
      if PermGood b.1 18 then (0 : ℝ≥0∞) else 1),
    Assembly.uavg_fst_marg (fun π : Equiv.Perm (X × Z) ↦ if PermGood π 18 then (0 : ℝ≥0∞) else 1),
    uavg_ite_zero_one, mul_comm, ← div_eq_mul_inv]
  exact permTerm_le_keccak

end bridge

/-! ## The chain -/

section chain

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The event side over `FullES` at `msgPol`** (EventSide's `uavg_p2R_msgPol_le_es'` at every
`(PK.seed, π, h)` with `PermGood π 18`, GoodES's `uavg_not_goodES_le`): at most
`eventTermS q cfEps + 2 goodESCap + 2^-777`. -/
theorem uavg_p2R_msgPol_full_le (hq : q ≤ 2 ^ 64) :
    uavg (fun ω : FullES ↦ p2R msgPol A (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2) ≤
      eventTermS q cfEps + 2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) := by
  rw [Assembly.uavg_prod_iter]
  have hpt : ∀ a : PublicParameter × Equiv.Perm (X × Z) × (Z → X),
      uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        p2R msgPol A (pubES a.1 a.2.1 a.2.2 θ.1) θ.2) ≤
      eventTermS q cfEps + 2 * uavg (fun θ ↦ if GoodES a.1 a.2.1 a.2.2 θ then (0 : ℝ≥0∞) else 1) +
        (if PermGood a.2.1 18 then 0 else 1) := fun a ↦ by
    by_cases hπ : PermGood a.2.1 18
    · rw [ite_eq_left hπ, add_zero]
      exact uavg_p2R_msgPol_le_es' hperm hsign a.1 a.2.1 a.2.2 hπ hq
    · rw [ite_eq_right hπ]
      refine le_trans ?_ le_add_self
      exact uavg_le_one_of_le fun θ ↦ p2R_le_one A msgPol _ _
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add, uavg_const, uavg_const_mul]
  refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
    uavg_not_permGood_es
  exact (Assembly.uavg_prod_iter (fun ω : FullES ↦
    if GoodES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2 then (0 : ℝ≥0∞) else 1)).symm.trans_le uavg_not_goodES_le

open scoped Classical in
set_option synthInstance.maxSize 2000 in
/-- **leanSPHINCS's win probability through the masked hybrid**: G0 is runtime 1 with the full
table (`winProb_eq_uavg_p1R`), the masked graded hybrid (`uavg_p1R_le`, masses `hS`, `hRd` on
`FullG S`, bad fraction `stageFrac S` paid once), the table average of runtime 2 moved to the
template data (`uavg_p2R_tab_le` on `FullG S`, with the win's mismatch term `winChgAvg A S` and
`stageFrac S` again, inside the event term) and the event side over `FullES`
(`uavg_p2R_msgPol_full_le`). -/
theorem winProb_le_masked (hq : q ≤ 2 ^ 64) (S : PP → ((s : HPos) → XD s) → Prop)
    (Hh : FT → Set Z) (Hk Hk' : FT → Set X)
    (hcov : ∀ t, Covers (fullHw (tabOf t)) (Hh t) (Hk t) (Hk' t)) (κ ν : ℝ≥0∞)
    (hS : uavg (fun t : FT ↦ if FullG S t then (runtimeR m0R).totalWeight .instruments
      (spongeMass (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)))
        initR else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * κ)
    (hRd : uavg (fun t : FT ↦ if FullG S t then (runtimeR m0R).totalWeight .instruments
      (readMass (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)))
        initR else 0) ≤ ν) :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A ≤
      ((eventTermS q cfEps + 2 * goodESCap + ENNReal.ofReal (1 / 2 ^ 777) +
          winChgAvg A S + stageFrac S) ^ (2⁻¹ : ℝ) + hybTermS q κ ν) ^ 2 +
        stageFrac S := by
  rw [winProb_eq_uavg_p1R]
  refine (uavg_p1R_le hperm hsign S Hh Hk Hk' hcov κ ν hS hRd).trans
    (add_le_add (pow_le_pow_left₀ zero_le (add_le_add (ENNReal.rpow_le_rpow ?_ (by norm_num))
      le_rfl) 2) le_rfl)
  refine (uavg_p2R_tab_le A S).trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  rw [uavg_pubP_eq_full]
  exact uavg_p2R_msgPol_full_le hperm hsign hq

end chain

end Quantum.Sphincs.Assembly

end
