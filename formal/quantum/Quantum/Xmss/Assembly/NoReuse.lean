module

public import Quantum.Xmss.Assembly.RecOffDecHit
public import Quantum.Xmss.Assembly.CwReFail
public import Quantum.Xmss.NoReuse

@[expose] public section

/-!
# Without leaf reuse the other labels' hits are empty

RecBadMass's `RecHitB`: a trial's `h`-read whose recorded value hits the selected digest of the
trial's key, selected by a block of another search. Against an adversary that requests no leaf
twice (`NoLeafReuse`), every key has at most one revealed label: a bottom key `e` is the leaf `e`,
and a top key `b` always signs its bottom root `v (.inl (tpos bottomLayer layerHeight b))`. So a
selected key is selected by the trial's own search, and `RecHitB` is empty on every run.

* **The bottom reveals** (`botRevCharge`, `chgLeaf_prefixR`): the record ports revealing a bottom
  label of key `e` (and the reads changing the revealed set) are charged one; the realized challenge
  prefix has charge at most one, from `NoLeafReuse` through the challenger and the realization.
* **The budget** (`forallQueries_of_charge_budget`): CostRun's `forallQueries_of_charge_step` with
  the remaining budget; at a port of charge `κ i` the counter is at most `t + n - κ i`. With the
  counter `botCnt e` (a bottom label of `e` revealed), no bottom label of `e` is revealed before a
  record port revealing one (`botGuard`).
* **The top labels** (`TopOk`, `topModed_prefixT`, `topModed_realizeT`): modes remembering the
  values of the last reveal; every reveal reveals one label or none, and a top label of key `b`
  carries the remembered value at `tpos bottomLayer layerHeight b` (PrefixFacts'
  `botRootPos_mem_layerNeed`). After realizing, the remembered values are those of `v` (`TauV`).
* **The invariant** (`KeyUniq`, `TopCanon`, `SelLab`, `NRInv`, `nrInvP_step`,
  `forallQueries_nrInv`): on the memory, one revealed label per layer and key, the top labels
  canonical, every selection a trial block of a revealed label of its key from the label's base,
  and in a search of `lab` from `base`, `lab` revealed and `base = v (.inr lab)`. Presented with a
  state guard (`forallQueries_of_modedP_sguard`).
* **No other-label hit** (`not_recHitB_of_nrInv`, `recHitBPre_eq_zero`, `recHitBAvg_zero`): a hit
  needs the key selected (`xmssTgtHw_cwBlk`), whose selecting label is the trial's (`KeyUniq`),
  from the same base: a re-grind (`RegrindSel`).
-/

universe u v w u₁ v₁

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Support invariants along runs -/

section generic

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- **The counter at every call, with the remaining budget** (CostRun's
`forallQueries_of_charge_step`): if port `i` raises the counter `g` of the support by at most
`κ i`, a program of charge at most `n` from support on counters at most `t` presents every call
of a port `i` an operator supported on counters at most `t + n - κ i`. -/
theorem forallQueries_of_charge_budget (g : R.D → ℕ) (κ : spec.Port → ℕ)
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + κ i))
          ((R.step i).branch r σ))
    {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec Ω A) {n : ℕ} (hx : IFreeM.IsChargeBound x (portCharge κ) n)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    R.ForallQueries I (fun i E σ ↦
      QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ g m.1.2) (Set.Iic (t + n - κ i)) σ)
      x ρ := by
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ _ => trivial
  | primBind _ o k ih =>
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [QuantumRuntime.forallQueries_primBind_iff]
    exact fun b ↦ ih b (hx b) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (isChargeBound_portCharge_queryBind_iff κ i E ℓ k n).mp hx
    rw [QuantumRuntime.forallQueries_queryBind_iff]
    refine ⟨?_, fun r ↦ ?_⟩
    · have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
        (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
          obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
          rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
      exact h₁.mono (Set.Iic_subset_Iic.2 (by omega))
    · have he : t + κ i + (n - κ i) = t + n := by omega
      exact (ih r (hk r) (QuerySupportedOn.queryStep_of_charge_step R g κ hR i E ℓ r hρ)).mono I
        fun _ _ _ h ↦ he ▸ h

/-- A family of conditions on the presented operators holds together. -/
theorem forallQueries_forall {L : LocalSig.{u, v}} {I : L.Interp} {Ω : QReg → Type w} {A : QReg}
    {ι : Type*} {P : ι → ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {x : QuantumComp L spec Ω A} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : ∀ e, R.ForallQueries I (P e) x ρ) :
    R.ForallQueries I (fun i E σ ↦ ∀ e, P e i E σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b fun e ↦ h e b
  | queryBind _ i E ℓ k ih => exact ⟨fun e ↦ (h e).1, fun r ↦ ih r fun e ↦ (h e).2 r⟩

end generic

section moded

variable {spec : QuantumOracleSpec.{0, 0}} {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}
  (R : QuantumRuntime spec) (I : Λ.Interp)

/-- **A support invariant per mode with a state guard** (RecOffDecHit's
`forallQueries_of_modedP_guard`, the guard on the presented operators): if every allowed call
keeps the support from the invariant of its mode within the guard of its port to the invariant
of the next mode, a moded program whose calls are presented operators within the guards, run from
an operator supported on the invariant of its first mode, presents every call an operator
supported on the invariant of a mode allowing it. -/
theorem forallQueries_of_modedP_sguard {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} (Inv : Mode → Set R.D)
    (G : spec.Port → Set R.D)
    (hstep : ∀ μ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), ok μ i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) (Inv μ ∩ G i) σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) (Inv (nx μ i r)) ((R.step i).branch r σ))
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp Λ spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ},
      R.ForallQueries I (fun i E σ ↦
        QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ m.1.2) (G i) σ) x ρ →
      QuerySupportedOn (fun m : A × R.D ↦ m.2) (Inv μ) ρ →
      R.ForallQueries I (fun i E σ ↦ ∃ μ, ok μ i ∧
        QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ m.1.2) (Inv μ) σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro μ hx ρ hg hρ
    rw [QuantumRuntime.forallQueries_primBind_iff] at hg ⊢
    exact fun b ↦ ih b μ (hx.2 (ULift.up b)) (hg b)
      (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hg hρ
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hg ⊢
    have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
      (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := Inv μ) fun m hm ↦ by
        obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
        rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
    refine ⟨⟨μ, hx.1, h₁⟩, fun r ↦ ih r _ (hx.2 (ULift.up r)) (hg.2 r) ?_⟩
    rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
    have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ m.2)
      (q' := fun m : spec.Out i × R.D ↦ m.2) (fun σ hσ ↦ hstep μ i r σ hx.1 hσ)
      (querySupportedOn_inter h₁ hg.1)
    refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
    obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
    rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- Casting the initial register keeps a moded property. -/
theorem modedP_cast_mode {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {Ω' : QReg → Type w}
    {fin : (Σ u, Ω' u) → Mode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω' A) (μ : Mode) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

end moded

/-! ## The memory along the ports of `runtimeR` -/

section memStep

/- Instance search for the run families over the register `PReg` exceeds the default size
(as in PrefixRun). -/
set_option synthInstance.maxSize 2000

/-- The memory a read port's outcome reports (the memory before the read). -/
def readPre : (c : HwRead X Z Mem) → c.Result → Mem
  | .readH _ _, r => r.2
  | .readK _ _, r => r.2
  | .readK' _ _, r => r.2

/-- The memory after a read port with outcome `r`. -/
def readMem : (c : HwRead X Z Mem) → c.Result → Mem
  | .readH _ u, r => u r.2 r.1
  | .readK _ u, r => u r.2 r.1
  | .readK' _ u, r => u r.2 r.1

theorem readMem_fst {c : HwRead X Z Mem} (hc : LabKeep c) (r : c.Result) :
    (readMem c r).1 = (readPre c r).1 := by
  cases c with
  | readH z u => exact hc _ _
  | readK x u => exact hc _ _
  | readK' x u => exact hc _ _

theorem memStep_sponge (p : SpongePort) (r : (recHwSpec X Z HPos Selections).Result
      (.inl (.inl (.inl p)))) {U U' : Set (HwReg X Z Mem)}
    (hU : ∀ s s' : HwReg X Z Mem, s'.2 = s.2 → s ∈ U → s' ∈ U')
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × HwReg X Z Mem)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × HwReg X Z Mem) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) ×
      HwReg X Z Mem ↦ m.2) U σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inl (.inl p))) ×
      HwReg X Z Mem ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inl (.inl p)))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inl (.inl p)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m0R p q.1 q'.1 q.2 q'.2 hK) hq

theorem memStep_read (c : HwRead X Z Mem) (r : c.Result) {U U' : Set (HwReg X Z Mem)}
    (hU : ∀ s s' : HwReg X Z Mem, s.2.2 = readPre c r → s'.2 = (s.2.1, readMem c r) → s ∈ U →
      s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inl (.inr c)))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at hK
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero hK).2
    exact hU q.2 q'.2 hp hφ hq

theorem memStep_prog (c : HwProg X Z) (r : c.Result) {U U' : Set (HwReg X Z Mem)}
    (hU : ∀ s s' : HwReg X Z Mem, s'.2.2 = s.2.2 → s ∈ U → s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inr c))).branch r σ) := by
  have hb : ((runtimeR (X := X) (Z := Z) m0R).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (by rw [hwProgKraus_ne_zero_snd c r hK]) hq

theorem memStep_rec (T : Finset HPos) (r : Finset HPos × Selections) {U U' : Set (HwReg X Z Mem)}
    (hU : ∀ s s' : HwReg X Z Mem, s'.2.2 = (s.2.2.1 ∪ T, s.2.2.2) → s ∈ U → s' ∈ U')
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (hσ : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U σ) :
    QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) U'
      (((runtimeR (X := X) (Z := Z) m0R).step (.inr T)).branch r σ) := by
  show QuerySupportedOn _ _ ((recStep (X := X) (Z := Z) T).branch r σ)
  rw [recStep_branch]
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hU q.2 q'.2 (congrArg Prod.snd (recKraus_ne_zero hK)) hq

/-- The initial operator holds the initial memory. -/
theorem querySupportedOn_initR_mem :
    QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z Mem ↦ m.2.2.2) {m0R} initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · show m.2.2.2 ∈ ({m0R} : Set Mem) ∧ m'.2.2.2 ∈ ({m0R} : Set Mem)
    rw [← he.1, ← he.2]
    exact ⟨Set.mem_singleton _, Set.mem_singleton _⟩
  · exact absurd rfl h

end memStep

/-! ## The bottom reveals -/

section bottom

/-- A bottom label of key `e` is in `T`. -/
def BotRev (e : KeyIndex) (T : Finset HPos) : Prop :=
  ∃ msg : Message, (.inr (.inl (e, msg)) : HPos) ∈ T

/-- **The bottom-label reveals of key `e`**: a record port revealing a bottom label of `e`, and a
read changing the revealed set, cost one. -/
noncomputable def botRevCharge (e : KeyIndex) : (recHwSpec X Z HPos Selections).Port → ℕ
  | .inl (.inl (.inr c)) => @ite _ (LabKeep c) (Classical.propDecidable _) 0 1
  | .inr T => @ite _ (BotRev e T) (Classical.propDecidable _) 1 0
  | _ => 0

/-- `botRevCharge` on the template's ports. -/
noncomputable def botRevChargeT (e : KeyIndex) : (XSpec Selections).Port → ℕ
  | .inl (.inl (.inr c)) => @ite _ (LabKeep c.1) (Classical.propDecidable _) 0 1
  | .inr T => @ite _ (BotRev e T) (Classical.propDecidable _) 1 0
  | _ => 0

/-- The counter: a bottom label of key `e` is revealed. -/
noncomputable def botCnt (e : KeyIndex) (s : HwReg X Z Mem) : ℕ :=
  @ite _ (BotRev e s.2.2.1) (Classical.propDecidable _) 1 0

theorem botCnt_of {e : KeyIndex} {s : HwReg X Z Mem} (h : BotRev e s.2.2.1) : botCnt e s = 1 := by
  unfold botCnt
  rw [ite_eq_left h]

theorem botCnt_of_not {e : KeyIndex} {s : HwReg X Z Mem} (h : ¬BotRev e s.2.2.1) :
    botCnt e s = 0 := by
  unfold botCnt
  rw [ite_eq_right h]

theorem botCnt_le_one (e : KeyIndex) (s : HwReg X Z Mem) : botCnt e s ≤ 1 := by
  unfold botCnt
  split_ifs <;> omega

theorem botCnt_congr {e : KeyIndex} {s s' : HwReg X Z Mem} (h : s'.2.2.1 = s.2.2.1) :
    botCnt e s' = botCnt e s := by
  unfold botCnt
  rw [h]

theorem botRevCharge_rec_of {e : KeyIndex} {T : Finset HPos} (h : BotRev e T) :
    botRevCharge e (.inr T) = 1 := by
  show @ite ℕ (BotRev e T) (Classical.propDecidable _) 1 0 = 1
  rw [ite_eq_left h]

theorem botRevChargeT_of_not {e : KeyIndex} {T : Finset HPos} (h : ¬BotRev e T) :
    botRevChargeT e (.inr T) = 0 := by
  show @ite ℕ (BotRev e T) (Classical.propDecidable _) 1 0 = 0
  rw [ite_eq_right h]

/-- **Every port of `runtimeR` raises the counter by at most its charge.** -/
theorem botCnt_step (e : KeyIndex) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ botCnt e m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ botCnt e m.2) (Set.Iic (t + botRevCharge e i))
      (((runtimeR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  have hσ' : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦
      m.2) {s | botCnt e s ≤ t} σ := hσ.imp fun _ h ↦ h
  refine (?_ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × HwReg X Z Mem ↦
      m.2) {s | botCnt e s ≤ t + botRevCharge e i} _).imp fun _ h ↦ h
  rcases i with ((p | c) | c) | T
  · exact memStep_sponge p r (fun s s' h hs ↦
      (botCnt_congr (congrArg (fun b ↦ b.2.1) h)).trans_le hs) σ hσ'
  · by_cases hk : LabKeep c
    · have h0 : botRevCharge e (.inl (.inl (.inr c))) = 0 := by
        show @ite ℕ (LabKeep c) (Classical.propDecidable _) 0 1 = 0
        rw [ite_eq_left hk]
      rw [h0]
      refine memStep_read c r (fun s s' hpre hpost hs ↦ ?_) σ hσ'
      have hT : s'.2.2.1 = s.2.2.1 := by
        rw [congrArg (fun b ↦ b.2.1) hpost]
        exact (readMem_fst hk r).trans (congrArg Prod.fst hpre).symm
      exact (botCnt_congr hT).trans_le hs
    · have h1 : botRevCharge e (.inl (.inl (.inr c))) = 1 := by
        show @ite ℕ (LabKeep c) (Classical.propDecidable _) 0 1 = 1
        rw [ite_eq_right hk]
      rw [h1]
      exact memStep_read c r (fun _ s' _ _ _ ↦
        (botCnt_le_one e s').trans (Nat.le_add_left 1 t)) σ hσ'
  · exact memStep_prog c r (fun s s' h hs ↦
      (botCnt_congr (congrArg Prod.fst h)).trans_le hs) σ hσ'
  · by_cases hT : BotRev e T
    · rw [botRevCharge_rec_of hT]
      exact memStep_rec T r (fun _ s' _ _ ↦
        (botCnt_le_one e s').trans (Nat.le_add_left 1 t)) σ hσ'
    · have h0 : botRevCharge e (.inr T) = 0 := by
        show @ite ℕ (BotRev e T) (Classical.propDecidable _) 1 0 = 0
        rw [ite_eq_right hT]
      rw [h0]
      refine memStep_rec T r (fun s s' h hs ↦ ?_) σ hσ'
      show botCnt e s' ≤ t + 0
      refine le_trans ?_ (show botCnt e s ≤ t from hs)
      by_cases hs' : BotRev e s'.2.2.1
      · obtain ⟨msg, hm⟩ := hs'
        rw [congrArg Prod.fst h] at hm
        rcases Finset.mem_union.mp hm with hm | hm
        · rw [botCnt_of ⟨msg, hm⟩]
          exact botCnt_le_one e s'
        · exact absurd ⟨msg, hm⟩ hT
      · rw [botCnt_of_not hs']
        exact Nat.zero_le _

theorem botCnt_initR (e : KeyIndex) :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ botCnt e m.2)
      (Set.Iic 0) initR :=
  querySupportedOn_initR_mem.imp fun m hm ↦ (botCnt_of_not fun ⟨_, h⟩ ↦ by
    rw [Set.mem_singleton_iff.mp hm] at h
    exact Finset.notMem_empty _ h).le

/-! ### The charge of the realized challenge prefix -/

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- Realizing keeps the bottom-reveal charge. -/
theorem chgRev_realizeT (e : KeyIndex) (v : HPos → Digest) {A : QReg}
    {y : QuantumComp L (XSpec Selections) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (botRevChargeT e)) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge (botRevCharge e)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (botRevCharge e) s ((tmplLens v).toFunA s cmd)) =
      portCharge (botRevChargeT e) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs makes no bottom reveal. -/
theorem chgRev_readLift (e : KeyIndex) {A : QReg}
    (y : QuantumComp L (hwReadSpec X Z Selections) Ω A) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (botRevChargeT e)) 0 := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  refine isChargeBound_mono_charge (fun s cmd ↦ ?_) (isChargeBound_zero y)
  rcases cmd with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show @ite ℕ (LabKeep (liftRead (S := HPos) c)) (Classical.propDecidable _) 0 1 ≤ 0
    rw [ite_eq_left (labKeep_liftRead c)]

theorem chgRev_revealThen (e : KeyIndex) {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (XSpec Selections) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (botRevChargeT e)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (botRevChargeT e))
      (botRevChargeT e (.inr T) + n) :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right _ _, fun r ↦ by
    rw [Nat.add_sub_cancel_left]
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := n) (chg_act _ _ 0) fun _ ↦ hk r).mono
      (Nat.zero_add n).le⟩

theorem chgRev_progThen (e : KeyIndex) {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD)
    (hp : goodAll p) (k : QComp (XSpec Selections) B B' α)
    (hk : IFreeM.IsChargeBound k (portCharge (botRevChargeT e)) 0) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (botRevChargeT e)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk⟩

theorem chgRev_progPorts (e : KeyIndex) (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts Selections B ps) (portCharge (botRevChargeT e)) 0 := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact chgRev_progThen e p trivial _ ih

theorem chgRev_progSlots (e : KeyIndex) (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots Selections pub B ss) (portCharge (botRevChargeT e)) 0 := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgRev_progPorts e B _) fun _ ↦ ih

/-- **A layer signature** reveals at most its own label. -/
theorem chgRev_signLayerT (e : KeyIndex) (pub : Pub) (B : QReg) (lab : RLabel) :
    IFreeM.IsChargeBound (signLayerT Selections cwUpd pub B lab) (portCharge (botRevChargeT e))
      (botRevChargeT e (.inr {.inr lab})) := by
  unfold signLayerT
  refine chgRev_revealThen e _ _ (n := 0) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgRev_readLift e _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · trivial
  · refine IFreeM.IsChargeBound.mono (chgRev_revealThen e _ _ (n := 0) fun _ ↦ ?_)
      (botRevChargeT_of_not (e := e) (T := inlSet (layerNeed lab.layer lab.key x))
        fun ⟨_, h⟩ ↦ inr_not_mem_inlSet h).le
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgRev_progSlots e pub B _)
      fun _ ↦ trivial

theorem botRevChargeT_botLabel (e : KeyIndex) (r : SigningRequest) :
    botRevChargeT e (.inr {.inr (botLabel r)}) ≤ leafCharge e (.sign r) := by
  show @ite ℕ (BotRev e {.inr (botLabel r)}) (Classical.propDecidable _) 1 0 ≤
    if r.leafIndex = e then 1 else 0
  by_cases h : r.leafIndex = e
  · rw [ite_eq_left h]
    split_ifs <;> omega
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨msg, hm⟩
    obtain ⟨he, -⟩ := Prod.mk.inj (Sum.inl_injective (Sum.inr_injective
      (Finset.mem_singleton.mp hm)))
    exact h (Fin.ext (by rw [he, keyIndexOnLayer_bottom_val]))

/-- **A signature** reveals a bottom label of `e` only for the leaf `e`. -/
theorem chgRev_signT (e : KeyIndex) (pub : Pub) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT Selections cwUpd pub B r) (portCharge (botRevChargeT e))
      (leafCharge e (.sign r)) := by
  unfold signT
  refine (FreeM₂.isChargeBound_bind (n₂ := 0) (chgRev_signLayerT e pub B _) fun b ↦ ?_).mono
    (botRevChargeT_botLabel e r)
  rcases b with _ | ⟨bottom, f⟩
  · trivial
  · refine (FreeM₂.isChargeBound_bind (n₂ := 0) (chgRev_signLayerT e pub B _) fun t ↦ ?_).mono
      (botRevChargeT_of_not fun ⟨_, h⟩ ↦ absurd (Sum.inr_injective (Finset.mem_singleton.mp h))
        (by simp [topLabel])).le
    rcases t with _ | ⟨top, _⟩ <;> trivial

/-- **The challenger** reveals a bottom label of `e` only at a request of the leaf `e`. -/
theorem chgRev_challengeT (e : KeyIndex) (pub : Pub) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    IFreeM.IsChargeBound (challengeT Selections cwUpd pub A cmd) (portCharge (botRevChargeT e))
      (cmdCharge (leafCharge e) A cmd) := by
  rcases cmd with o | ⟨p | r, E, ℓ⟩
  · exact chgRev_readLift e _
  · exact chgRev_readLift e _
  · exact IFreeM.isChargeBound_bind (n₂ := 0) ((FreeM₂.isChargeBound_bind (n₁ := 0)
      (chg_act _ _ 0) fun _ ↦ chgRev_signT e pub _ r).mono (Nat.zero_add _).le)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0

/-- **The challenge prefix** of an adversary reusing no leaf reveals a bottom label of `e` at
most once. -/
theorem chgRev_prefixT {A : Adversary (X × Z)} (hleaf : NoLeafReuse A) (e : KeyIndex)
    (pub : Pub) :
    IFreeM.IsChargeBound (prefixT Selections cwUpd pub A) (portCharge (botRevChargeT e)) 1 := by
  unfold prefixT
  refine (chgRev_revealThen e _ _ (n := 1) fun _ ↦ ?_).mono (le_of_eq (by
    rw [botRevChargeT_of_not fun ⟨_, h⟩ ↦ by simp at h, Nat.zero_add]))
  exact FreeM₂.isChargeBound_bind (n₁ := 1) (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (challengeT Selections cwUpd pub)
      (c := cmdCharge (leafCharge e)) (fun s cmd ↦ chgRev_challengeT e pub s cmd)
      (isChargeBound_withSignLog (hleaf _ e))) fun _ ↦ trivial

/-- **The realized challenge prefix** of an adversary reusing no leaf reveals a bottom label of
`ℓ` at most once. -/
theorem chgLeaf_prefixR {A : Adversary (X × Z)} (hleaf : NoLeafReuse A) (ℓ : KeyIndex) (pub : Pub)
    (v : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A))
      (portCharge (botRevCharge ℓ)) 1 :=
  chgRev_realizeT ℓ v (chgRev_prefixT hleaf ℓ pub)

end bottom

/-! ## The top labels -/

section top

/-- The modes of the top labels: the values of the last reveal at the value positions. -/
abbrev TopMode : Type := ValPos → Option Digest

/-- The values a reveal returns at the value positions, `none` off them. -/
def optVals {T : Finset HPos} (w : RevealVals XD T) (p : ValPos) : Option Digest :=
  if h : (.inl p : HPos) ∈ T then some (w ⟨.inl p, h⟩) else none

/-- **A reveal the top labels allow**: one label or none, a top label of key `b` carrying the
remembered value at `tpos bottomLayer layerHeight b`. -/
def TopOk (τ : TopMode) (T : Finset HPos) : Prop :=
  (∀ lab : RLabel, (.inr lab : HPos) ∈ T → T = {.inr lab}) ∧
    ∀ (e : KeyIndex) (d : Digest), (.inr (.inr (e, d)) : HPos) ∈ T →
      τ (tpos bottomLayer layerHeight e.val) = some d

/-- The remembered values are those of `v`. -/
def TauV (v : HPos → Digest) (τ : TopMode) : Prop :=
  ∀ p d, τ p = some d → d = v (.inl p)

/-- The calls the top modes allow, on the template's ports. -/
def topOkT (τ : TopMode) : (XSpec Selections).Port → Prop
  | .inr T => TopOk τ T
  | _ => True

/-- The top mode after a call of the template. -/
def topNxT (τ : TopMode) : (i : (XSpec Selections).Port) → (XSpec Selections).Result i → TopMode
  | .inr _, r => optVals r.1
  | _, _ => τ

/-- The calls the top modes allow, on runtime 2's ports with record ports. -/
def topOkZ (τ : TopMode) : (recHwSpec X Z HPos Selections).Port → Prop
  | .inr T => TopOk τ T
  | _ => True

/-- The top mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
def topNxZ (v : HPos → Digest) (τ : TopMode) :
    (i : (recHwSpec X Z HPos Selections).Port) → (recHwSpec X Z HPos Selections).Result i →
      TopMode
  | .inr T, _ => optVals (restrictTo (D := XD) T v)
  | _, _ => τ

theorem tauV_optVals (v : HPos → Digest) (T : Finset HPos) :
    TauV v (optVals (restrictTo (D := XD) T v)) := by
  intro p d h
  unfold optVals at h
  split_ifs at h with hp
  exact (Option.some.inj h).symm

theorem topOk_single {τ : TopMode} {lab : RLabel}
    (h : ∀ e d, lab = .inr (e, d) → τ (tpos bottomLayer layerHeight e.val) = some d) :
    TopOk τ {.inr lab} :=
  ⟨fun lab' h' ↦ by rw [Sum.inr_injective (Finset.mem_singleton.mp h')],
    fun e d h' ↦ h e d (Sum.inr_injective (Finset.mem_singleton.mp h')).symm⟩

/-- **Realizing keeps the top modes.** -/
theorem topModed_realizeT (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → TopMode → Prop} (y : QuantumComp L (XSpec Selections) Ω A)
    {τ : TopMode} (hy : ModedP topOkT topNxT fin τ y) :
    ModedP topOkZ (topNxZ v) fin τ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing τ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ τ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))⟩

/-- Runtime 1's programs keep the top modes. -/
theorem topModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → TopMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z Selections) Ω A) :
    ∀ τ, (∀ p, fin p τ) → ModedP topOkT topNxT fin τ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun τ h ↦ h _
  | liftBind _ c next ih =>
    intro τ h
    show ModedP _ _ _ τ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ τ h⟩
    · exact ⟨trivial, fun b ↦ ih _ τ h⟩
    · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> exact ⟨trivial, fun b ↦ ih _ τ h⟩

theorem topModed_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (XSpec Selections) B B' α)
    {F : α → TopMode → Prop} {τ : TopMode} (hT : TopOk τ T)
    (hk : ∀ r, ModedP topOkT topNxT (fun p τ' ↦ F p.2.2 τ') (optVals r.1) (k r)) :
    ModedP topOkT topNxT (fun p τ' ↦ F p.2.2 τ') τ (revealThen goodAll T k) :=
  ⟨hT, fun b ↦ modedP₂_bind (F := fun _ τ' ↦ τ' = optVals b.down.1) _ _ ⟨trivial, fun _ ↦ rfl⟩
    fun _ τ' h ↦ by subst h; exact hk b.down⟩

theorem topModed_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec Selections) B B' α) {F : α → TopMode → Prop} {τ : TopMode}
    (hk : ModedP topOkT topNxT (fun q τ' ↦ F q.2.2 τ') τ k) :
    ModedP topOkT topNxT (fun q τ' ↦ F q.2.2 τ') τ (progThen p hp k) :=
  ⟨trivial, fun _ ↦ modedP₂_bind (F := fun _ τ' ↦ τ' = τ) _ _ ⟨trivial, fun _ ↦ rfl⟩
    fun _ τ' h ↦ by subst h; exact hk⟩

theorem topModed_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD))
    {F : Unit → TopMode → Prop} {τ : TopMode} (h : F () τ) :
    ModedP topOkT topNxT (fun q τ' ↦ F q.2.2 τ') τ (progPorts Selections B ps) := by
  induction ps with
  | nil => exact h
  | cons p ps ih => exact topModed_progThen p trivial _ ih

theorem topModed_progSlots (pub : Pub) (B : QReg) (ss : List Slot) {F : Unit → TopMode → Prop}
    {τ : TopMode} (h : F () τ) :
    ModedP topOkT topNxT (fun q τ' ↦ F q.2.2 τ') τ (progSlots Selections pub B ss) := by
  induction ss with
  | nil => exact h
  | cons s ss ih =>
    exact modedP₂_bind (F := fun _ τ' ↦ τ' = τ) _ _
      (topModed_progPorts B _ (F := fun _ τ' ↦ τ' = τ) rfl) fun _ τ' h' ↦ by subst h'; exact ih

/-- The output of a layer signature: its values are the remembered ones at the coordinates it
reveals. -/
def LayerOut (lab : RLabel) (o : Option (LayerSignature × (ValPos → Digest))) (τ : TopMode) :
    Prop :=
  ∀ sig f, o = some (sig, f) → ∃ x : Encoding, ∀ q ∈ layerNeed lab.layer lab.key x, τ q = some (f q)

/-- **A layer signature** remembers the values it returns. -/
theorem topModed_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) {τ : TopMode}
    (hlab : TopOk τ {.inr lab}) :
    ModedP topOkT topNxT (fun p τ' ↦ LayerOut lab p.2.2 τ') τ
      (signLayerT Selections cwUpd pub B lab) := by
  refine topModed_revealThen _ _ hlab fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ τ' ↦ τ' = optVals r₀.1) _ _
    (topModed_readLift _ _ fun _ ↦ rfl) fun g τ' h ↦ ?_
  subst h
  rcases g with _ | ⟨ρ, x⟩
  · intro sig f h
    cases h
  · refine topModed_revealThen _ _ ⟨fun lab' h ↦ absurd h inr_not_mem_inlSet,
      fun e d h ↦ absurd h inr_not_mem_inlSet⟩ fun r ↦ ?_
    refine modedP₂_bind (F := fun _ τ' ↦ τ' = optVals r.1) _ _
      (topModed_progSlots pub B _ (F := fun _ τ' ↦ τ' = optVals r.1) rfl) fun _ τ' h ↦ ?_
    subst h
    intro sig f hsf
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hsf)
    refine ⟨x, fun q hq ↦ ?_⟩
    unfold optVals extendVals
    rw [dite_eq_left (inl_mem_inlSet.mpr hq), dite_eq_left (inl_mem_inlSet.mpr hq)]

/-- **A signature**: the top label carries the bottom root the bottom layer revealed. -/
theorem topModed_signT (pub : Pub) (B : QReg) (r : SigningRequest) (τ : TopMode) :
    ModedP topOkT topNxT (fun _ _ ↦ True) τ (signT Selections cwUpd pub B r) := by
  refine modedP₂_bind (F := fun o τ' ↦ LayerOut (botLabel r) o τ') (F' := fun _ _ ↦ True) _ _
    (topModed_signLayerT pub B _ (topOk_single fun e d h ↦ by simp [botLabel] at h))
    fun b τ' hb ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · trivial
  · obtain ⟨x, hx⟩ := hb bottom f rfl
    have hroot : τ' (botRootPos r) = some (f (botRootPos r)) :=
      hx _ (botRootPos_mem_layerNeed r x)
    refine modedP₂_bind (F := fun o τ'' ↦ LayerOut (topLabel r (f (botRootPos r))) o τ'')
      (F' := fun _ _ ↦ True) _ _ (topModed_signLayerT pub B _ (topOk_single fun e d h ↦ ?_))
      fun t _ _ ↦ ?_
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inr_injective h)
      exact hroot
    · rcases t with _ | ⟨top, _⟩ <;> trivial

theorem topModed_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) (τ : TopMode) :
    ModedP topOkT topNxT (fun _ _ ↦ True) τ (challengeT Selections cwUpd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact topModed_readLift _ τ fun _ ↦ trivial
  · exact topModed_readLift _ τ fun _ ↦ trivial
  · exact modedP_bind _ _ (modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
      ⟨trivial, fun _ ↦ trivial⟩ fun _ τ' _ ↦ topModed_signT pub _ r τ') fun _ _ _ _ ↦ trivial

theorem topModed_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec Selections)))
    (hσ : ∀ A c τ, ModedP topOkT topNxT (fun _ _ ↦ True) τ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ τ, ModedP topOkT topNxT (fun _ _ ↦ True) τ (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ ↦ trivial
  | liftBind s c next ih =>
    intro τ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c τ) fun u ans τ' _ ↦
      (modedP_cast_mode ans.2 _ _).mpr (ih ans.1 τ')

/-- **The challenge prefix is moded by the top modes.** -/
theorem topModed_prefixT (pub : Pub) (A : Adversary (X × Z)) (τ : TopMode) :
    ModedP topOkT topNxT (fun _ _ ↦ True) τ (prefixT Selections cwUpd pub A) :=
  topModed_revealThen _ _ (F := fun _ _ ↦ True)
    ⟨fun lab h ↦ by simp at h, fun e d h ↦ by simp at h⟩ fun _ ↦
      modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
        (topModed_substitute _ (topModed_challengeT pub) _ _) fun _ _ _ ↦ trivial

end top

/-! ## The invariant -/

section inv

/-- One revealed label per layer and key. -/
def KeyUniq (T : Finset HPos) : Prop :=
  ∀ lab lab' : RLabel, (.inr lab : HPos) ∈ T → (.inr lab' : HPos) ∈ T →
    lab.layer = lab'.layer → lab.key = lab'.key → lab = lab'

/-- Every revealed top label of key `b` carries `v` at `tpos bottomLayer layerHeight b`. -/
def TopCanon (v : HPos → Digest) (T : Finset HPos) : Prop :=
  ∀ (e : KeyIndex) (d : Digest), (.inr (.inr (e, d)) : HPos) ∈ T →
    d = v (.inl (tpos bottomLayer layerHeight e.val))

/-- **Every selection is a trial block of a revealed label of its key**, from the label's base. -/
def SelLab (P : PublicParameter) (v : HPos → Digest) (m : Mem) : Prop :=
  ∀ l e sel, m.2 l e = some sel → ∃ lab : RLabel, (.inr lab : HPos) ∈ m.1 ∧
    lab.layer = l ∧ lab.key = e ∧ ∃ j, sel.1 = cwBlk P lab (v (.inr lab)) j

/-- The invariant between searches. -/
def NRGlob (P : PublicParameter) (v : HPos → Digest) (m : Mem) : Prop :=
  KeyUniq m.1 ∧ TopCanon v m.1 ∧ SelLab P v m

/-- The search of a mode: its label and base. -/
def CwMode.search : CwMode → Option (RLabel × Randomizer)
  | .free => none
  | .grd lab base _ => some (lab, base)
  | .afK lab base _ _ => some (lab, base)
  | .afK' lab base _ _ _ => some (lab, base)

/-- The invariant on the memory, within a search of `lab` from `base`: `lab` revealed and
`base = v (.inr lab)`. -/
def NRMem (P : PublicParameter) (v : HPos → Digest) : Option (RLabel × Randomizer) → Mem → Prop
  | none, m => NRGlob P v m
  | some (lab, base), m => NRGlob P v m ∧ (.inr lab : HPos) ∈ m.1 ∧ base = v (.inr lab)

/-- **The invariant of a search mode.** -/
def NRInv (P : PublicParameter) (v : HPos → Digest) (μ : CwMode) : Set (HwReg X Z Mem) :=
  {s | NRMem P v μ.search s.2.2}

/-- The invariant of the product modes. -/
def NRInvP (P : PublicParameter) (v : HPos → Digest) (μ : CwMode × TopMode) :
    Set (HwReg X Z Mem) :=
  {s | TauV v μ.2 ∧ s ∈ NRInv P v μ.1}

/-- **The state guard**: no bottom label of a key is revealed before a reveal of one. -/
def botGuard (i : (recHwSpec X Z HPos Selections).Port) : Set (HwReg X Z Mem) :=
  {s | ∀ e, botCnt e s ≤ 0 + 1 - botRevCharge e i}

variable {P : PublicParameter} {v : HPos → Digest}

theorem nrGlob_of_nrMem {o : Option (RLabel × Randomizer)} {m : Mem} (h : NRMem P v o m) :
    NRGlob P v m := by
  rcases o with _ | ⟨lab, base⟩
  · exact h
  · exact h.1

theorem nrInv_congr {μ μ' : CwMode} {s s' : HwReg X Z Mem} (hm : s'.2.2 = s.2.2)
    (hμ : μ'.search = μ.search) (hs : s ∈ NRInv P v μ) : s' ∈ NRInv P v μ' := by
  show NRMem P v μ'.search s'.2.2
  rw [hm, hμ]
  exact hs

theorem nrInv_free {μ : CwMode} {s s' : HwReg X Z Mem} (hm : s'.2.2 = s.2.2)
    (hs : s ∈ NRInv P v μ) : s' ∈ NRInv P v .free := by
  show NRGlob P v s'.2.2
  rw [hm]
  exact nrGlob_of_nrMem hs

theorem cwUpd_eq_some {l : Layer} {e : KeyIndex} {x xi : X} {m : Selections} {o : Option X}
    {l' : Layer} {e' : KeyIndex} {sel : X × Digest} (h : cwUpd l e x xi m o l' e' = some sel) :
    m l' e' = some sel ∨ (l' = l ∧ e' = e ∧ sel.1 = x) := by
  rcases o with _ | w
  · exact .inl h
  · rcases cwUpd_some l e x xi m w with h' | h'
    · rw [h'] at h
      exact .inl h
    · rw [h'] at h
      unfold cwSel at h
      split_ifs at h
      · rw [select_apply] at h
        split_ifs at h with hle
        · exact .inr ⟨hle.1, hle.2, by rw [← Option.some.inj h]⟩
        · exact .inl h
      · exact .inl h

/-- **A trial's `h`-read keeps the invariant of its search.** -/
theorem nrMem_cwUpd {lab : RLabel} {base : Randomizer} {m : Mem}
    (h : NRMem P v (some (lab, base)) m) (j : ℕ) (xi : X) (o : Option X) :
    NRMem P v (some (lab, base)) (m.1, cwUpd lab.layer lab.key (cwBlk P lab base j) xi m.2 o) := by
  obtain ⟨⟨hk, ht, hs⟩, hr, hb⟩ := h
  refine ⟨⟨hk, ht, fun l e sel hsel ↦ ?_⟩, hr, hb⟩
  rcases cwUpd_eq_some hsel with h | ⟨rfl, rfl, h⟩
  · exact hs l e sel h
  · exact ⟨lab, hr, rfl, rfl, j, by rw [h, hb]⟩

/-- **A record keeps the invariant between searches**: a revealed bottom label is the only one of
its key (`hb`), a revealed top label is canonical (`TopOk`, `TauV`). -/
theorem nrGlob_rec {m : Mem} {τ : TopMode} {T : Finset HPos} (hg : NRGlob P v m)
    (hτ : TauV v τ) (hT : TopOk τ T) (hb : ∀ e, BotRev e T → ¬BotRev e m.1) :
    NRGlob P v (m.1 ∪ T, m.2) := by
  obtain ⟨hk, htc, hs⟩ := hg
  have hno : ∀ lab lab' : RLabel, (.inr lab : HPos) ∈ T → (.inr lab' : HPos) ∈ m.1 →
      lab.layer = lab'.layer → lab.key = lab'.key → lab = lab' := by
    intro lab lab' h h' hl hk'
    rcases lab with ⟨e, msg⟩ | ⟨e, d⟩ <;> rcases lab' with ⟨e', msg'⟩ | ⟨e', d'⟩
    · obtain rfl : e = e' := hk'
      exact absurd ⟨msg', h'⟩ (hb e ⟨msg, h⟩)
    · exact absurd hl bottomLayer_ne_topLayer
    · exact absurd hl.symm bottomLayer_ne_topLayer
    · obtain rfl : e = e' := hk'
      rw [hτ _ _ (hT.2 e d h), htc e d' h']
  refine ⟨fun lab lab' h h' hl hk' ↦ ?_, fun e d h ↦ ?_, fun l e sel h ↦ ?_⟩
  · rcases Finset.mem_union.mp h with h | h <;> rcases Finset.mem_union.mp h' with h' | h'
    · exact hk lab lab' h h' hl hk'
    · exact (hno lab' lab h' h hl.symm hk'.symm).symm
    · exact hno lab lab' h h' hl hk'
    · rw [hT.1 lab h] at h'
      exact (Sum.inr_injective (Finset.mem_singleton.mp h')).symm
  · rcases Finset.mem_union.mp h with h | h
    · exact htc e d h
    · exact hτ _ _ (hT.2 e d h)
  · obtain ⟨lab, hm, rest⟩ := hs l e sel h
    exact ⟨lab, Finset.mem_union_left _ hm, rest⟩

/- Instance search for the run families over the register `PReg` exceeds the default size
(as in PrefixRun). -/
set_option synthInstance.maxSize 2000

/-- **Every allowed call keeps the invariant of its product mode**, within the guard. -/
theorem nrInvP_step (π : Equiv.Perm (X × Z)) (μ : CwMode × TopMode)
    (i : (recHwSpec X Z HPos Selections).Port) (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem)
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) ℂ)
    (hok : cwOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ.1 i ∧ topOkZ μ.2 i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
      (NRInvP P v μ ∩ botGuard i) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × HwReg X Z Mem ↦ m.2)
      (NRInvP P v (dwNxZ π P v μ.1 i r, topNxZ v μ.2 i r))
      (((runtimeR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  obtain ⟨μ, τ⟩ := μ
  rcases i with ((p | c) | c) | T
  · refine memStep_sponge p r ?_ σ hσ
    intro s s' h hs
    exact ⟨hs.1.1, nrInv_free (congrArg Prod.snd h) hs.1.2⟩
  · rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
      rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    all_goals try exact False.elim hok.1
    · obtain ⟨-, -, rfl⟩ := hok.1
      refine memStep_read (.readK x fun m _ ↦ m) r ?_ σ hσ
      intro s s' hpre hpost hs
      exact ⟨hs.1.1, nrInv_congr ((congrArg Prod.snd hpost).trans hpre.symm) rfl hs.1.2⟩
    · obtain ⟨-, rfl⟩ := hok.1
      refine memStep_read (.readK' y fun m _ ↦ m) r ?_ σ hσ
      intro s s' hpre hpost hs
      exact ⟨hs.1.1, nrInv_congr ((congrArg Prod.snd hpost).trans hpre.symm) rfl hs.1.2⟩
    · obtain ⟨-, rfl⟩ := hok.1
      refine memStep_read (.readH z' (cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi)) r ?_
        σ hσ
      intro s s' hpre hpost hs
      refine ⟨hs.1.1, ?_⟩
      have hm' : NRMem P v (some (lab, base)) s'.2.2 := by
        rw [congrArg Prod.snd hpost]
        show NRMem P v (some (lab, base))
          (r.2.1, cwUpd lab.layer lab.key (cwBlk P lab base j) xi r.2.2 r.1)
        rw [show r.2 = s.2.2 from hpre.symm]
        exact nrMem_cwUpd hs.1.2 j xi r.1
      show NRMem P v (dwOut lab base j (out256 (xi + r.1.getD 0))).search s'.2.2
      unfold dwOut
      split_ifs
      · exact hm'.1
      · exact hm'
  · refine memStep_prog c r ?_ σ hσ
    intro s s' h hs
    exact ⟨hs.1.1, nrInv_free h hs.1.2⟩
  · refine memStep_rec T r ?_ σ hσ
    intro s s' h hs
    refine ⟨tauV_optVals v T, ?_⟩
    have hg : NRGlob P v (s.2.2.1 ∪ T, s.2.2.2) := nrGlob_rec (nrGlob_of_nrMem hs.1.2) hs.1.1
      hok.2 fun e he hold ↦ by
        have h1 := hs.2 e
        rw [botRevCharge_rec_of he, botCnt_of hold] at h1
        omega
    show NRMem P v (cwRevNx T fun lab ↦ v (.inr lab)).search s'.2.2
    rw [h]
    unfold cwRevNx cwOptNx
    rcases hl : cwRevLab T with _ | lab
    · exact hg
    · refine ⟨hg, Finset.mem_union_right _ ?_, rfl⟩
      rw [cwRevLab_spec hl]
      exact Finset.mem_singleton_self _

theorem nrInvP_initR :
    QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z Mem ↦ m.2)
      (NRInvP P v (.free, fun _ ↦ none)) initR := by
  refine querySupportedOn_initR_mem.imp fun m hm ↦ ⟨fun _ _ h ↦ (by cases h), ?_⟩
  show NRGlob P v m.2.2.2
  rw [Set.mem_singleton_iff.mp hm]
  exact ⟨fun _ _ h ↦ absurd h (Finset.notMem_empty _),
    fun _ _ h ↦ absurd h (Finset.notMem_empty _), fun _ _ _ h ↦ by cases h⟩

/-- **The invariant at the calls of the realized challenge prefix**: against an adversary that
reuses no leaf, every call is presented an operator supported on the invariant of a mode allowing
it. -/
theorem forallQueries_nrInv {A : Adversary (X × Z)} (hleaf : NoLeafReuse A) (pub : Pub)
    (v : HPos → Digest) :
    (runtimeR m0R).ForallQueries .instruments (fun i E σ ↦ ∃ μ : CwMode,
      cwOkZ pub.perm pub.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
        QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) × E ↦
          m.1.2) (NRInv pub.param v μ) σ)
      (realizeT v (prefixT Selections cwUpd pub A)) initR := by
  have hg : (runtimeR m0R).ForallQueries .instruments (fun i E σ ↦
      QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) × E ↦
        m.1.2) (botGuard i) σ) (realizeT v (prefixT Selections cwUpd pub A)) initR :=
    (forallQueries_forall (runtimeR m0R) fun e ↦ forallQueries_of_charge_budget (runtimeR m0R)
      (botCnt e) (botRevCharge e) (botCnt_step e) .instruments _ (chgLeaf_prefixR hleaf e pub v)
      (botCnt_initR e)).mono .instruments fun _ _ _ h m m' hm ↦
        ⟨fun e ↦ (h e m m' hm).1, fun e ↦ (h e m m' hm).2⟩
  have h := forallQueries_of_modedP_sguard (runtimeR m0R) .instruments (NRInvP pub.param v)
    botGuard (fun μ i r σ hok hσ ↦ nrInvP_step pub.perm μ i r σ hok hσ) _ (.free, fun _ ↦ none)
    (modedP_prod _ _ _ (dwModedP_prefixR cwUpd pub A v)
      (topModed_realizeT v _ (topModed_prefixT pub A _))) hg nrInvP_initR
  exact h.mono .instruments fun _ _ _ ⟨μ, hok, hσ⟩ ↦ ⟨μ.1, hok.1, hσ.mono fun _ hs ↦ hs.2⟩

end inv

/-! ## No other-label hit -/

section noHit

/-- **No other-label hit on the invariant**: a hit needs the trial's key selected; the selecting
label is revealed with the trial's layer and key, so it is the trial's label (`KeyUniq`), from the
trial's base: a re-grind. -/
theorem not_recHitB_of_nrInv {L : HonestTable} {v : HPos → Digest} {μ : CwMode}
    {c : HwRead X Z Mem} (hok : cwRdOk L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ c)
    (ht : IsTrial trialUpd c) {s : HwReg X Z Mem} (hs : s ∈ NRInv L.param v μ) :
    ¬RecHitB L (trialOf trialUpd c).1 (trialOf trialUpd c).2 s := by
  rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
    rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
  all_goals try exact False.elim hok
  · obtain ⟨_, h⟩ := ht
    cases h
  · obtain ⟨_, h⟩ := ht
    cases h
  · obtain ⟨hzz, rfl⟩ := hok
    subst z'
    have hc := eq_readH_trialOf trialUpd ht
    obtain ⟨-, hu'⟩ := HwRead.readH.inj hc
    obtain ⟨hl, he, hx, -⟩ := trialUpd_inj
      (t := ⟨lab.layer, lab.key, cwBlk L.param lab base j, xi⟩)
      (t' := (trialOf trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem)).2)
      (by rw [← hu']; rfl)
    rintro ⟨⟨_, _, _, htgt⟩, hnr⟩
    obtain ⟨⟨hku, -, hsl⟩, hrev, hbase⟩ := hs
    rw [hx] at htgt
    obtain ⟨sel, hm, -, -⟩ := xmssTgtHw_cwBlk htgt
    obtain ⟨lab', hrev', hl', he', j', hj'⟩ := hsl _ _ sel hm
    obtain rfl := hku lab lab' hrev hrev' hl'.symm he'.symm
    refine hnr ⟨sel, by rw [hl, he]; exact hm, lab, base, j, j', hx, ?_⟩
    rw [hj', hbase]

/-- A trial read port presented an operator on the invariant has no `RecHitB` mass. -/
theorem recHitBW_eq_zero {L : HonestTable} {v : HPos → Digest} {μ : CwMode} {c : HwRead X Z Mem}
    (hok : cwRdOk L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ c)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hs : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) (NRInv L.param v μ) σ) :
    recHitBW L c σ = 0 := by
  unfold recHitBW
  split_ifs with ht
  · refine ENNReal.ofReal_eq_zero.mpr (le_of_eq (Finset.sum_eq_zero fun q _ ↦ ?_))
    by_cases hq : σ q q = 0
    · rw [hq, Complex.zero_re, ite_self]
    · rw [ite_eq_right (not_recHitB_of_nrInv hok ht (hs q q hq).1)]
  · rfl

variable {A : Adversary (X × Z)} (hleaf : NoLeafReuse A)
include hleaf

/-- **Without leaf reuse the `RecHitB` mass vanishes.** -/
theorem recHitBPre_eq_zero (L : HonestTable) : recHitBPre A L = 0 := by
  refine le_antisymm ((totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
        (NRInv L.param (valueAt L) μ) σ)
    (fun _ _ _ ⟨μ, hok, hσ⟩ ↦ ⟨μ, hok, querySupportedOn_traceRight hσ⟩)
    (w' := fun i σ ↦ 0 * extWeight (hwCost (recHitBW L) fun _ _ ↦ 0) i σ)
    (fun i σ _ hI ↦ ?_) (prefixR A L) initR_posSemidef
    (forallQueries_nrInv hleaf (pubOf L) (valueAt L))).trans
      (le_of_eq ((totalWeight_const_mul_weight (runtimeR m0R) .instruments 0 _ (prefixR A L)
        initR).trans (zero_mul _)))) zero_le
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · obtain ⟨μ, hok, hs⟩ := hI
    show recHitBW L c σ ≤ _
    rw [recHitBW_eq_zero hok hs]
    exact zero_le
  · exact zero_le
  · exact zero_le

/-- **Without leaf reuse `RecHitBAvg` holds at `0`.** -/
theorem recHitBAvg_zero (good : HonestTable → Prop) [DecidablePred good] :
    RecHitBAvg A good 0 := by
  unfold RecHitBAvg
  simp only [recHitBPre_eq_zero hleaf, ite_self]
  exact uavg_const_le 0

end noHit

end Quantum.Xmss.Assembly

end
