module

public import Quantum.Xmss.Assembly.RecHitB
public import Quantum.Xmss.Assembly.RecOffDecHit

@[expose] public section

/-!
# The decompressed other-label hits

RecHitB reduces `RecHitBAvg` to `DecHitBAvg`: the decompressed weight of a trial's `h`-read whose
cell makes the trial's tail hit the selected digest of its key, selected by a block of another
search. Here that weight is bounded by the weight of a decompressed event on the register.

* **The label is revealed in its search** (`RevI`, `HInv`, `forallQueries_hInv`): RecOffDecHit's
  persistence invariant `DInv` and, in a search of `lab`, `lab` among the revealed labels.
* **A hit is a first codeword of a revealed label equal to another search's selection**
  (`OtherHit`, `HitBEv`, `hitBEv_of_hitGB`): on the invariant, a hit at trial `j` of `lab` makes
  `j` the first codeword of `lab`'s search in the view, its digest the key's selected digest,
  selected by a block outside the search (`¬ RegrindSel`), unless a trial reads a programmable
  cell (`LabHit`).
* **The weight of the reads** (`decHitBW_le_potential`, `decHitBPre_le_hbPre`): each trial read
  weighs at most the decompressed weight of `HitBEv` (`hbQ`), summed along the prefix as `hbPre`.
* **A potential raised by increments** (`totalWeight_le_charge_potential_add`,
  `totalWeight_le_charge_potential_inv`, `hbPre_le`): with the sponge ports keeping the weight of
  `HitBEv` (`tsum_potential_hbQ_sponge`) and the step condition `HbStep` on the other ports,
  `hbPre ≤ clsCap · (initial weight + increments)`, the increments (`incSet`, `incW`, `incPre`)
  the registers a record or an `h`-read switches into `HitBEv`. The initial weight is the trial
  event's (`potential_hbQ_initR_le`: no label revealed).
* **The average** (`decHitBAvg_goodL`): `DecHitBAvg A GoodL (2^-74 + clsCap · ε)` from `HbStep`
  on the good tables and `IncAvg A GoodL ε`.

The remaining lemmas:
* `HbStep L`: in the decompressed basis a read, program or record call is classical on the
  register (the view is kept, a program moves it only at a table cell, the memory moves
  deterministically given the branch), and `HitBEv` is determined off the table, so the call
  moves the weight of `HitBEv` by at most the weight of `incSet`.
* `IncAvg A GoodL ε`: the increments. At a selecting `h`-read they vanish on CwReFail's `FInv`
  (the revealed labels of an unselected key failed every trial run, so no first codeword equals
  the new selection). At a first reveal of a label `lab` whose key is selected they are the
  weight of "the first codeword of `lab`'s search from its base is the selected digest": the base
  is undisclosed until the reveal, the trial blocks it gives are recorded with the mass of CwRev's
  `firstW`, and on unrecorded blocks the trial's cells decompress to fresh uniform values, so each
  trial costs `2^-128` plus the leak `2/|Z|`. With at most `2 lifetime` reveals of `2^32` trials,
  `ε ≈ 2^-63 + O(q 2^-94)`. A static fraction over label pairs fails: the labels range over
  `2^256` messages each, chosen adaptively.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The event -/

section event

variable (L : HonestTable)

/-- **The search of `lab` stops at trial `j` with digest `d`** in the view `t`: its earlier
trials' digests are no codewords, trial `j`'s is the codeword `d`. -/
def FirstCw (t : SpongeKeys X Z) (lab : RLabel) (j : ℕ) (d : Digest) : Prop :=
  j < randomizerAttemptLimit ∧ trialDg t L.perm (labBlk L lab j) = d ∧ Codeword.Valid d ∧
    ∀ i < j, ¬ Codeword.Valid (trialDg t L.perm (labBlk L lab i))

/-- **A revealed label stops at its key's selection, made by another search**: the selected
block is no block of the label's search, and the label's search stops at the selected digest. -/
def OtherHit (s : HwReg X Z Mem) : Prop :=
  ∃ lab : RLabel, (Sum.inr lab : HPos) ∈ s.2.2.1 ∧ ∃ sel, s.2.2.2 lab.layer lab.key = some sel ∧
    (∀ n, sel.1 ≠ labBlk L lab n) ∧ ∃ j, FirstCw L (regFns s) lab j sel.2

/-- **The event of the other-label hits**: a trial reads a programmable cell, or `OtherHit`. -/
def HitBEv (s : HwReg X Z Mem) : Prop :=
  LabHit L (regFns s) ∨ OtherHit L s

open scoped Classical in
/-- **The projector on the event** in the decompressed basis. -/
noncomputable def hbQ : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ :=
  hwDecProj {s : HwReg X Z Mem | HitBEv L s}

end event

/-! ## The searched label is revealed -/

section revI

variable (L : HonestTable)

/-- In a search of `lab`, `lab` is revealed. -/
def RevI : CwMode → Set (HwReg X Z Mem)
  | .free => Set.univ
  | .grd lab _ _ => {s | (Sum.inr lab : HPos) ∈ s.2.2.1}
  | .afK lab _ _ _ => {s | (Sum.inr lab : HPos) ∈ s.2.2.1}
  | .afK' lab _ _ _ _ => {s | (Sum.inr lab : HPos) ∈ s.2.2.1}

/-- **The invariant**: RecOffDecHit's `DInv` and `RevI`. -/
def HInv (μ : CwMode) : Set (HwReg X Z Mem) :=
  DInv L μ ∩ RevI μ

variable {L}

/- Instance search for the run families over the register `PReg` exceeds the default size
(as in PrefixRun). -/
set_option synthInstance.maxSize 2000

theorem querySupportedOn_univ' {α β : Type*} (q : α → β) (σ : Matrix α α ℂ) :
    QuerySupportedOn q Set.univ σ :=
  fun _ _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- **Every allowed call keeps `RevI`**: reads keep the revealed labels, a reveal of one label
starts its search with the label revealed. -/
theorem revI_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ)
    (hok : cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2)
      (RevI μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × PReg ↦ m.2)
      (RevI (dwNxZ L.perm L.param (valueAt L) μ i r))
      (((decR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact querySupportedOn_univ' _ _
  · rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
      rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    all_goals try exact False.elim hok
    · obtain ⟨-, rfl, rfl⟩ := hok
      refine (decR_readU_supp m0R (.readK (cwBlk L.param lab base j) keepMem) r _ σ hσ).mono ?_
      rintro s' ⟨s, hs, -, rfl⟩
      exact hs
    · obtain ⟨rfl, rfl⟩ := hok
      refine (decR_readU_supp m0R (.readK' (L.perm (cwBlk L.param lab base j, a)).1 keepMem) r _ σ
        hσ).mono ?_
      rintro s' ⟨s, hs, -, rfl⟩
      exact hs
    · obtain ⟨hzz, rfl⟩ := hok
      subst z'
      refine (decR_readU_supp m0R (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi))
        r _ σ hσ).mono ?_
      rintro s' ⟨s, hs, -, rfl⟩
      show _ ∈ RevI (dwOut lab base j (out256 (xi + r.1.getD 0)))
      unfold dwOut
      split_ifs
      · trivial
      · exact hs
  · exact querySupportedOn_univ' _ _
  · refine (decR_rec_supp m0R T r _ σ hσ).mono ?_
    rintro s' ⟨s, -, -, rfl⟩
    show _ ∈ RevI (cwRevNx T fun lab ↦ valueAt L (.inr lab))
    unfold cwRevNx cwOptNx
    rcases h : cwRevLab T with _ | lab
    · trivial
    · show (Sum.inr lab : HPos) ∈ s.2.2.1 ∪ T
      rw [cwRevLab_spec h]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **Every allowed call of a program in the table keeps the invariant of its mode.** -/
theorem hInv_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ)
    (hok : cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i)
    (hin : PortIn Selections (tableHw L) i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2)
      (HInv L μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × PReg ↦ m.2)
      (HInv L (dwNxZ L.perm L.param (valueAt L) μ i r))
      (((decR (X := X) (Z := Z) m0R).step i).branch r σ) :=
  querySupportedOn_inter (dInv_step μ i r σ hok hin (hσ.mono fun _ h ↦ h.1))
    (revI_step μ i r σ hok (hσ.mono fun _ h ↦ h.2))

theorem hInv_init :
    QuerySupportedOn (fun m : QReg.of Unit × PReg ↦ m.2) (HInv L .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) :=
  querySupportedOn_inter dInv_init (querySupportedOn_univ' _ _)

/-- **The invariant at the calls of the prefix, in the decompressed basis.** -/
theorem forallQueries_hInv_dec (A : Adversary (X × Z)) :
    (decR (X := X) (Z := Z) m0R).ForallQueries .instruments (fun i E σ ↦ ∃ μ,
      cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
        QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × PReg) × E ↦ m.1.2)
          (HInv L μ) σ) (prefixR A L)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) :=
  forallQueries_of_modedP_guard (decR m0R) .instruments (HInv L) (PortIn Selections (tableHw L))
    (fun μ i r σ hok hin hσ ↦ hInv_step μ i r σ hok hin hσ) (prefixR A L) .free
    (dwModedP_prefixR cwUpd (pubOf L) A (valueAt L)) (forallQueries_portIn_dec A) hInv_init

/-- **The invariant at the calls of the prefix**: every call is presented an operator whose
decompressed form is supported on the invariant of a mode allowing it. -/
theorem forallQueries_hInv (A : Adversary (X × Z)) :
    (runtimeR m0R).ForallQueries .instruments (fun i E τ ↦ ∃ μ,
      cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
        QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (HInv L μ)
          (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
            ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem)
            (MatrixMap.traceRight _ E τ))) (prefixR A L) initR := by
  have hC : compressReg X Z Mem * compressReg X Z Mem = 1 := compressReg_mul_self
  have hstep : ∀ i r, ((runtimeRH (X := X) (Z := Z) m0R).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft ((recHwSpec X Z HPos Selections).In i) =
      (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft ((recHwSpec X Z HPos Selections).Out i) ∘ₗ
        ((decR m0R).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m0R) (compressReg X Z Mem) compressReg_mul_self
      conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation .instruments (R₁ := decR m0R)
    (R₂ := runtimeRH (X := X) (Z := Z) m0R) (V := MatrixMap.conj (compressReg X Z Mem)) hstep
    (P₂ := fun i E τ ↦ ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (HInv L μ)
        (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem)
          (MatrixMap.traceRight _ E τ)))
    (fun i E τ ⟨μ, hok, hτ⟩ ↦ ⟨μ, hok, by
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight
        (q := fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) hτ⟩)
    (forallQueries_hInv_dec A)
  have hρ' : (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft (QReg.of Unit)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) = initR := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z Mem)), conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

end revI

/-! ## A hit is the event -/

section hit

variable {L : HonestTable}

/-- **An other-label hit is `HitBEv`**: at trial `j` of `lab` the earlier trials' digests in the
view are no codewords and the trial's digest is the view's; the hit makes it the key's selected
digest, a codeword (`SelCons`), selected by a block outside the search (`¬ RegrindSel`), and
`lab` is revealed (`RevI`). -/
theorem hitBEv_of_hitGB {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z : Z} {t : TrialPt}
    (hl : t.l = lab.layer) (he : t.e = lab.key) (hx : t.x = cwBlk L.param lab base j)
    (hxi : trunc128 t.xi = trunc128 xi) {s : HwReg X Z Mem}
    (hs : s ∈ HInv L (.afK' lab base j xi z)) (h : hitGB L z t s.2 (s.1.1 z)) :
    HitBEv L s := by
  obtain ⟨⟨⟨⟨-, -, hsel⟩, hb, hlow⟩, hj, hmid, hz⟩, hrev⟩ := hs
  subst hb
  rcases hsel with hh | hsel
  · exact .inl hh
  right
  obtain ⟨hW, hnr, v, hv, htgt⟩ := h
  rw [hx] at htgt
  obtain ⟨sel, hm, -, hy⟩ := xmssTgtHw_cwBlk htgt
  obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hsel _ _ sel hm
  have hvz : (regFns s).1 z = v := by
    show ((s.2.1.1 z).or (s.1.1 z)).getD 0 = v
    rw [hW, hv]
    rfl
  have hdg : trialDg (regFns s) L.perm (cwBlk L.param lab (valueAt L (.inr lab)) j) = sel.2 := by
    unfold trialDg trialRate
    rw [← hz, hmid, hvz, ← hy]
    exact (trunc128_add_congr hxi v).symm
  refine ⟨lab, hrev, sel, hm, fun n hn ↦ hnr ⟨sel, by rw [hl, he]; exact hm, ?_⟩,
    j, hj, hdg, h3, hlow⟩
  rw [hx, hn]
  exact ⟨lab, valueAt L (.inr lab), j, n, rfl, rfl⟩

/-- **A call's decompressed other-label hit weight is at most the event's weight.** -/
theorem decHitBW_le_potential {μ : CwMode} {c : HwRead X Z Mem}
    (hok : cwRdOk L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ c)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) (HInv L μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    decHitBW L c σ ≤ potential (hbQ L) σ := by
  rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
    rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
  all_goals try exact False.elim hok
  · unfold decHitBW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · unfold decHitBW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · obtain ⟨hzz, rfl⟩ := hok
    subst z'
    have htr : IsTrial trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem) :=
      ⟨(z, ⟨lab.layer, lab.key, cwBlk L.param lab base j, xi⟩), rfl⟩
    have hc := eq_readH_trialOf trialUpd htr
    obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
    obtain ⟨hl, he, hx, hxi⟩ := trialUpd_inj
      (t := ⟨lab.layer, lab.key, cwBlk L.param lab base j, xi⟩)
      (t' := (trialOf trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem)).2)
      (by rw [← hu']; rfl)
    unfold decHitBW hbQ
    rw [ite_eq_left htr, potential_eq, conjTranspose_hwDecProj, hwDecProj_mul_self]
    refine ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le _ _ (HInv L (.afK' lab base j xi z))
      hσ hs fun s hsI hsE ↦ ?_)
    have hsE' : hitGB L z (trialOf trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem)).2
        s.2 (s.1.1 z) := by
      have h := hsE
      rw [← hz'] at h
      exact h
    exact hitBEv_of_hitGB hl he hx hxi hsI hsE'

end hit

/-! ## Along the prefix -/

section pre

/-- **The event's weight at the trial reads**, summed along the prefix. -/
noncomputable def hbPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ σ ↦ potential (hbQ L) σ) fun _ _ ↦ 0)) (prefixR A L) initR

/-- **The decompressed other-label hit weight along the prefix** is at most the event's weight at
the reads (`decHitBW_le_potential` on `forallQueries_hInv`). -/
theorem decHitBPre_le_hbPre (A : Adversary (X × Z)) (L : HonestTable) :
    decHitBPre A L ≤ hbPre A L :=
  totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2)
        (HInv L μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ))
    (fun _ _ _ h ↦ h)
    (fun i σ hσ hI ↦ by
      rcases i with ((p | c) | c) | T
      · exact zero_le
      · obtain ⟨μ, hok, hs⟩ := hI
        exact decHitBW_le_potential hok hσ hs
      · exact zero_le
      · exact zero_le) (prefixR A L) initR_posSemidef (forallQueries_hInv A)

end pre

/-! ## A charged potential raised by increments -/

section chargeGen

universe u v w

variable {spec : QuantumOracleSpec.{0, 0}} {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}
  (R : QuantumRuntime spec) (I : Λ.Interp)

/-- **A charged weight below a potential raised by increments**: if every call weighs at most its
charge times the potential of `K`, and raises that potential by at most `c`, a program of charge
at most `n` weighs at most `n` times the initial potential plus the increments along it. -/
theorem totalWeight_le_charge_potential_add {Zp : Type} [Fintype Zp] (K : Matrix Zp R.D ℂ)
    (κ : spec.Port → ℕ) (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ κ i * potential K σ)
    (hd : ∀ i (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), σ.PosSemidef →
      ∑' r, potential K ((R.step i).branch r σ) ≤ potential K σ + c i σ)
    {A : QReg} (x : QuantumComp Λ spec Ω A) :
    ∀ {n : ℕ}, IFreeM.IsChargeBound x (portCharge κ) n →
      ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
        R.totalWeight I w x ρ ≤ n * (potential K ρ + R.totalWeight I c x ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ =>
    intro n _ ρ _
    simp
  | primBind _ o k ih =>
    intro n hx ρ hρ
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [totalWeight_primBind, totalWeight_primBind]
    calc ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (n : ℝ≥0∞) * (potential K (((I o).frame R.D).branch b ρ) +
            R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ)) :=
          ENNReal.tsum_le_tsum fun b ↦
            ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ)
      _ = n * (∑' b, potential K (((I o).frame R.D).branch b ρ) +
            ∑' b, R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ _ := by
          gcongr
          exact tsum_potential_frame_le K (I o) hρ
  | queryBind _ i E ℓ k ih =>
    intro n hx ρ hρ
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    rw [totalWeight_queryBind, totalWeight_queryBind]
    have hσ := posSemidef_callInput ℓ hρ
    set S := ∑' r, R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ)
    have hs : ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) ≤
        ((n - κ i : ℕ) : ℝ≥0∞) * (potential K ρ + c i (callInput ℓ R.D ρ) + S) := by
      refine (ENNReal.tsum_le_tsum fun r ↦ ih r (hx.2 r)
        ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)).trans ?_
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) zero_le
      simp only [potential_queryStep]
      rw [← potential_callInput K ℓ ρ]
      exact hd i _ hσ
    have hw' : w i (callInput ℓ R.D ρ) ≤ κ i * (potential K ρ + c i (callInput ℓ R.D ρ) + S) := by
      rw [← potential_callInput K ℓ ρ]
      refine (hw i _ hσ).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      rw [add_assoc]
      exact le_self_add
    calc w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ)
        ≤ κ i * (potential K ρ + c i (callInput ℓ R.D ρ) + S) +
            ((n - κ i : ℕ) : ℝ≥0∞) * (potential K ρ + c i (callInput ℓ R.D ρ) + S) :=
          add_le_add hw' hs
      _ = n * (potential K ρ + (c i (callInput ℓ R.D ρ) + S)) := by
          rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hx.1, add_assoc]

/-- **`totalWeight_le_charge_potential_add` on an invariant**: the conditions only for inputs
satisfying `Inv`, when every call of the run is presented an operator satisfying `P`, which gives
`Inv`. -/
theorem totalWeight_le_charge_potential_inv {Zp : Type} [Fintype Zp] (K : Matrix Zp R.D ℂ)
    (κ : spec.Port → ℕ)
    (P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
    (Inv : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → Inv i σ → w i σ ≤ κ i * potential K σ)
    (hd : ∀ i (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), σ.PosSemidef → Inv i σ →
      ∑' r, potential K ((R.step i).branch r σ) ≤ potential K σ + c i σ)
    {A : QReg} (x : QuantumComp Λ spec Ω A) {n : ℕ}
    (hx : IFreeM.IsChargeBound x (portCharge κ) n) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) (hq : R.ForallQueries I P x ρ) :
    R.totalWeight I w x ρ ≤ n * (potential K ρ + R.totalWeight I c x ρ) := by
  classical
  have hw' : R.totalWeight I w x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then w i σ else 0) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hq
  have hc' : R.totalWeight I c x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then c i σ else ⊤) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hq
  rw [hw', hc']
  refine totalWeight_le_charge_potential_add R I K κ _ _ (fun i σ hσ ↦ ?_) (fun i σ hσ ↦ ?_) x hx hρ
  · by_cases hi : Inv i σ
    · rw [ite_eq_left hi]
      exact hw i σ hσ hi
    · rw [ite_eq_right hi]
      exact zero_le
  · by_cases hi : Inv i σ
    · rw [ite_eq_left hi]
      exact hd i σ hσ hi
    · rw [ite_eq_right hi, add_top]
      exact le_top

end chargeGen

/-! ## The event's weight along the prefix -/

section incr

variable (L : HonestTable)

/-- **The registers whose event a call can switch on**: a record of `T` adds `T` to the revealed
labels; an `h`-read updates the memory with the view's value. -/
def incSet : (recHwSpec X Z HPos Selections).Port → Set PReg
  | .inr T => {s | ¬ HitBEv L s ∧ HitBEv L (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))}
  | .inl (.inl (.inr (.readH z u))) =>
      {s | ¬ HitBEv L s ∧ HitBEv L (s.1, s.2.1, u s.2.2 ((hwView s.2.1 s.1).1 z))}
  | _ => ∅

open scoped Classical in
/-- **The increment of a call**: the decompressed weight of the registers whose event it can
switch on. -/
noncomputable def incW (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ) : ℝ≥0∞ :=
  potential (hwDecProj (incSet L i)) σ

/-- **The increments along the prefix.** -/
noncomputable def incPre (A : Adversary (X × Z)) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (incW L) (prefixR A L) initR

/-- **The remaining step condition**: on the invariant, an allowed read, program or record call
in the table raises the event's weight by at most its increment (in the decompressed basis these
calls are classical on the register; the event is determined off the table). -/
def HbStep : Prop :=
  ∀ (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ),
    σ.PosSemidef → (∀ p, i ≠ .inl (.inl (.inl p))) →
    cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i → PortIn Selections (tableHw L) i →
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (HInv L μ)
      (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
        ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ) →
    ∑' r, potential (hbQ L) (((runtimeR m0R).step i).branch r σ) ≤
      potential (hbQ L) σ + incW L i σ

/-- The calls' invariant: a mode allowing the call, the call in the table, the mode's invariant
of the decompressed input. -/
def CallInv (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ) : Prop :=
  ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧ PortIn Selections (tableHw L) i ∧
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (HInv L μ)
      (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
        ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ)

/-- **The sponge ports keep the event's weight** (in the decompressed basis they keep the
register). -/
theorem tsum_potential_hbQ_sponge (p : SpongePort)
    {σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × PReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × PReg) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' r, potential (hbQ L) (((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ) ≤
      potential (hbQ L) σ := by
  classical
  refine tsum_potential_branch_le (runtimeR m0R) _ _ (fun r ↦ ?_) hσ
  unfold hbQ
  cases p <;> exact branch_comm_of_commute
    (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R _ r) (hwPort_commute_hwDecProj _ _)

/-- **The initial weight of the event** is the trial event's: no label is revealed. -/
theorem potential_hbQ_initR_le : potential (hbQ L) initR ≤ potential (labQ L) initR := by
  classical
  unfold hbQ labQ
  simp only [potential_eq, conjTranspose_hwDecProj, hwDecProj_mul_self]
  refine ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le _ _ _ initR_posSemidef (init_dec m0R)
    fun s hsI hsE ↦ ?_)
  obtain ⟨-, hs⟩ := hsI
  have hW : s.2.1 = hwEmpty X Z := congrArg Prod.fst hs
  have hm : s.2.2.1 = ∅ := congrArg (fun p ↦ p.2.1) hs
  show LabHitD L s.1
  rcases (show HitBEv L s from hsE) with hh | ⟨lab, hl, -⟩
  · have hle : Quantum.Sponge.HwLe s.2.1 (tableHw L) := by
      rw [hW]
      exact ⟨fun z v h ↦ (by cases h), fun x v h ↦ (by cases h), fun x v h ↦ (by cases h)⟩
    exact labHitD_of_labHit hle hh
  · rw [hm] at hl
    exact absurd hl (Finset.notMem_empty _)

/-- A trial read's decompressed other-label hit weight is at most its trace. -/
theorem decHitBW_le_trace (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    decHitBW L c σ ≤ ENNReal.ofReal σ.trace.re := by
  unfold decHitBW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le_trace _ hσ)
  · exact zero_le

/-- **The remaining average**: over a good set, the average of the increments along the prefix
is at most `ε`. -/
def IncAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (ε : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then incPre L A else 0) ≤ ε

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The event's weight at the reads** is at most `clsCap` times its initial weight plus the
increments along the prefix. -/
theorem hbPre_le (hstep : HbStep L) :
    hbPre A L ≤ clsCap * (potential (hbQ L) initR + incPre L A) := by
  have hq := forallQueries_and (forallQueries_hInv (L := L) A) (forallQueries_hwSupp_prefixR A L)
  refine totalWeight_le_charge_potential_inv (runtimeR m0R) .instruments (hbQ L) _ _ (CallInv L)
    (fun i E τ h ↦ ?_) _ (incW L) (fun i σ _ _ ↦ ?_) (fun i σ hσ hI ↦ ?_) (prefixR A L)
    (clsCalls_prefixR hperm hsign L) initR_posSemidef hq
  · obtain ⟨⟨μ, hok, hs⟩, hp⟩ := h
    exact ⟨μ, hok, hp.1, hs⟩
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · show potential (hbQ L) σ ≤ ((if extCls X Z Mem (recSpec HPos Selections)
        (.inl (.inl (.inr c))) then 1 else 0 : ℕ) : ℝ≥0∞) * potential (hbQ L) σ
      simp [extCls, hwCls]
    · exact zero_le
    · exact zero_le
  · obtain ⟨μ, hok, hin, hs⟩ := hI
    rcases i with ((p | c) | c) | T
    · exact (tsum_potential_hbQ_sponge L p hσ).trans le_self_add
    · exact hstep μ _ σ hσ (fun p h ↦ by cases h) hok hin hs
    · exact hstep μ _ σ hσ (fun p h ↦ by cases h) hok hin hs
    · exact hstep μ _ σ hσ (fun p h ↦ by cases h) hok hin hs

/-- The decompressed other-label hit weight of any table is at most `clsCap`. -/
theorem decHitBPre_le_clsCap : decHitBPre A L ≤ clsCap :=
  (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
      fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ hσ ↦ by
        rcases i with ((p | c) | c) | T
        · exact zero_le
        · exact decHitBW_le_trace L c hσ
        · exact zero_le
        · exact zero_le) (prefixR A L) initR_posSemidef).trans
    (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))

omit hperm hsign in
open scoped Classical in
/-- **`DecHitBAvg` on Security's good tables** from the step condition and the increments:
`τ = 2^-74 + clsCap · ε` (`2^-75` for the initial trial event on the tables with
`TrialsOffAll`, `clsCap` on the `2^-173` others). -/
theorem decHitBAvg_goodL (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) {ε : ℝ≥0∞}
    (hstep : ∀ L, GoodL L → HbStep L) (hinc : IncAvg A GoodL ε) :
    DecHitBAvg A GoodL (ENNReal.ofReal (1 / 2 ^ 74) + clsCap * ε) := by
  unfold DecHitBAvg
  calc uavg (fun L ↦ if GoodL L then decHitBPre A L else 0)
      ≤ uavg (fun L ↦ (ENNReal.ofReal (1 / 2 ^ 75) +
          (clsCap : ℝ≥0∞) * (if TrialsOffAll L then (0 : ℝ≥0∞) else 1)) +
          (clsCap : ℝ≥0∞) * (if GoodL L then incPre L A else 0)) :=
        uavg_mono fun L ↦ by
          by_cases hL : GoodL L
          · rw [ite_eq_left hL, ite_eq_left hL]
            by_cases ho : TrialsOffAll L
            · rw [ite_eq_left ho, mul_zero, add_zero]
              calc decHitBPre A L ≤ clsCap * (potential (hbQ L) initR + incPre L A) :=
                    (decHitBPre_le_hbPre A L).trans (hbPre_le L hperm hsign (hstep L hL))
                _ = clsCap * potential (hbQ L) initR + clsCap * incPre L A := mul_add _ _ _
                _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_left ((potential_hbQ_initR_le L).trans
                    (potential_labQ_initR_le ho hL.1.1)) zero_le).trans
                      (decHitTerm_le (card_labBlocks_le L) (card_k'Cells_le L)
                        (card_hCells_le L))) le_rfl
            · rw [ite_eq_right ho, mul_one]
              exact (decHitBPre_le_clsCap L hperm hsign).trans (le_add_self.trans le_self_add)
          · rw [ite_eq_right hL, ite_eq_right hL]
            exact zero_le
    _ = uavg (fun _ : HonestTable ↦ ENNReal.ofReal (1 / 2 ^ 75)) +
          (clsCap : ℝ≥0∞) * uavg (fun L ↦ if TrialsOffAll L then (0 : ℝ≥0∞) else 1) +
          (clsCap : ℝ≥0∞) * uavg (fun L ↦ if GoodL L then incPre L A else 0) := by
        rw [uavg_add, uavg_add, uavg_const_mul, uavg_const_mul]
    _ ≤ (ENNReal.ofReal (1 / 2 ^ 75) + (clsCap : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 173)) +
          (clsCap : ℝ≥0∞) * ε :=
        add_le_add (add_le_add (uavg_const_le _) (mul_le_mul_of_nonneg_left (by
          rw [uavg_ite_zero_one]
          exact trialsOffAll_frac_le_keccak) zero_le)) (mul_le_mul_of_nonneg_left hinc zero_le)
    _ ≤ _ := add_le_add decHitTau_le le_rfl

end incr

end Quantum.Xmss.Assembly

end
