module

public import Quantum.Sphincs.Assembly.EncPorts
public import Quantum.Sphincs.Assembly.CostRun
public import Quantum.Xmss.Assembly.RecJ

@[expose] public section

/-!
# The `RecJ` weight of a run

EncPorts' `totalWeight_kJumpW_le` splits the program jump weight of a run into the target-free
fresh flips (`kfW`) and the `RecJ` weight (`recJW`): the programmed `k` (`k'`) cell is not
hardwired, the union is not good, and the union with the cell erased is good. This file bounds the
`RecJ` weight along a run of `runtimeR` and on the challenge prefix, as leanXMSS's
`Quantum.Xmss.Assembly.RecJ` (whose generic part is reused: the potential `recPotN`, `N` minus the
hardwired `k`, `k'` cells on a union that is not good, `0` on a good union; its level sets and its
program steps).

* **The ports** (`hS_rj`, `hR_rj`, `recJW_add_prog_rj`): on EncPorts' port invariant `PortInv` of a
  run with at most `n` sponge, `K` classical and `P` program calls, a sponge call raises the
  potential by at most `rjS (n + K) P`, a read by at most `rjR (n + K) P` per unit of trace (a trial
  read keeps it), a program inside a hardwired table pays its `RecJ` weight out of the potential up
  to `rjN P` times the target-free fresh flips; record ports keep it.
* **The run** (`totalWeight_recJW_le`): the `RecJ` weight is at most
  `n rjS + K rjR + rjN P · kfW`-total (the potential starts at `0`).
* **The prefix** (`recJPre`, `kfPre`, `recJPre_le`): on `prefixR pol A p v`, at data with
  `PermGood π 18`, for `q ≤ 2^64` and calls staying inside a hardwired table (`StaysIn`):
  `recJPre ≤ 6q rjS + clsCap rjR + rjN progCap · kfPre`.
* **The average** (`uavg_recJPre_le`, `recCapS`, `rjS_le`, `rjR_le`, `recCapS_le`): over a finite
  family of template data, from the averaged `kfPre` bound `κ`: at most
  `recCapS q κ ≤ 2^-36 + 2^43 κ` for `q ≤ 2^64`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z extProgCharge card_X)
open Quantum.Xmss.Hybrid (uavg uavg_mono diagMass diagMass_empty totalWeight_chargeTrace_le
  totalWeight_le_totalWeight totalWeight_add_weight totalWeight_const_mul_weight)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight extCls ProgOf hwKs recPotN
  recPotN_le recPotN_of_good portInst_recLev_k portInst_recLev_k' portInst_recLev_h
  recPotN_progK_le recPotN_progK'_le recPotN_progK_add_one_le recPotN_progK'_add_one_le
  recPotN_progH recPotN_offCell tsum_potential_readH_le ofReal_ind_add_le readPort
  readCost_le_of_keep keepE_le_of_portInst capKJ capKJ' capKJ_mono capKJ'_mono epsLev
  totalWeight_le_potential_of_forallQueries potential_basis_init tsum_potential_recStep_diag
  ofReal_trace_basis_init potential_diagPot_sqrt uavg_ite_le_add_mul uavg_const_le
  traceRight_diag_eq_zero forallQueries_and card_Z inv_two_pow_eq_ofReal
  isChargeBound_mono_charge)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## The constants -/

/-- **The weight of the potential**: `2P + 1`, more than the hardwired `k`, `k'` cells at
hardwired grade `P`. -/
def rjN (P : ℕ) : ℕ := 2 * P + 1

/-- **The charge of a sponge call** per unit of trace: `rjN P (2 √(6ε) + 6ε)`, `ε = epsQ nD P`. -/
noncomputable def rjS (nD P : ℕ) : ℝ := rjN P * (2 * √(6 * epsQ nD P) + 6 * epsQ nD P)

/-- **The charge of a `k`, `k'` read call** per unit of trace:
`rjN P (ε + 2/|X| + 2/|Z| + 2 √ε)`. -/
noncomputable def rjR (nD P : ℕ) : ℝ :=
  rjN P * (epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P))

theorem rjS_nonneg (nD P : ℕ) : 0 ≤ rjS nD P := by
  have := epsQ_nonneg nD P
  unfold rjS
  positivity

theorem rjR_nonneg (nD P : ℕ) : 0 ≤ rjR nD P := by
  have := epsQ_nonneg nD P
  unfold rjR
  positivity

/-! ## The ports -/

section ports

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem hwKs_lt_rjN {P : ℕ} {s : HwReg X Z (Finset S × M')} (h : dbGrade s.2.1 ≤ P) :
    hwKs s < rjN P := by
  have h1 : Database.size s.2.1.2.1 ≤ dbGrade s.2.1 := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : Database.size s.2.1.2.2 ≤ dbGrade s.2.1 := (le_max_right _ _).trans (le_max_right _ _)
  show Database.size s.2.1.2.1 + Database.size s.2.1.2.2 < 2 * P + 1
  omega

/-- **The sponge ports**: the potential rises by at most `rjS nD P` per unit of trace (two-sided
fresh bounds of the level sets; none at `h`). -/
theorem hS_rj (Ok : HwRead X Z (Finset S × M') → Prop) (π : Equiv.Perm (X × Z))
    (hπ : PermGood π 18) {nD P : ℕ} (m₀ : Finset S × M') (p : SpongePort)
    {σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inl p))) σ) :
    ∑' _r : Unit, potential (diagPot fun s ↦ √(recPotN π (rjN P) s : ℝ))
        (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
      potential (diagPot fun s ↦ √(recPotN π (rjN P) s : ℝ)) σ +
        ENNReal.ofReal (rjS nD P * σ.trace.re) := by
  have hsupp : QuerySupportedOn (fun m : spongeIn X Z p × HwReg X Z (Finset S × M') ↦ m.2)
      {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ nW P} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hε : ∀ (m : ℕ) (W : Hw X Z) (mm : Finset S × M'),
      PortInst (slice (levSet (recPotN π (rjN P)) (nW P) m) W mm) p (nD + 1)
        (ENNReal.ofReal (epsQ nD P)) := fun m W mm ↦ by
    cases p with
    | h => exact portInst_recLev_h π (rjN P) (nW P) m W mm _ _
    | k => exact portInst_recLev_k π hπ (rjN P) (nW P) nD m W mm
    | k' => exact portInst_recLev_k' π hπ (rjN P) (nW P) nD m W mm
  refine (tsum_potential_sponge_layer_le (recPotN π (rjN P)) (nW P) nD (rjN P)
    (fun s _ _ ↦ recPotN_le π (rjN P) s) (epsQ_nonneg nD P) (hwEmpty X Z) m₀ p hε hσ
    hsupp).trans (add_le_add le_rfl (le_of_eq (congrArg ENNReal.ofReal ?_)))
  unfold rjS
  ring

/-- **The read ports**: a `k`, `k'` read keeping the memory raises the potential by at most
`rjR nD P` per unit of trace; an `h` read keeps it. -/
theorem hR_rj (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')
    (π : Equiv.Perm (X × Z)) (hπ : PermGood π 18) {nD P : ℕ} (m₀ : Finset S × M')
    (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv (EncReadOk updOf) nD P m₀ (.inl (.inl (.inr c))) σ) :
    ∑' r, potential (diagPot fun s ↦ √(recPotN π (rjN P) s : ℝ))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(recPotN π (rjN P) s : ℝ)) σ +
        ENNReal.ofReal (rjR nD P * σ.trace.re) := by
  have hok : EncReadOk updOf c := hI.1
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2)
      {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ nW P} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hg : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ dbGrade m.2.1)
      (Set.Iic nD) σ :=
    hI.2.1.imp fun _ h ↦ Set.mem_Iic.mpr h.1
  have hcost : ∀ m, (∀ W mm, PortInst (slice (levSet (recPotN π (rjN P)) (nW P) m) W mm)
      (readPort c) (nD + 1) (ENNReal.ofReal (epsQ nD P))) → KeepUpd c →
      readCost (levSet (recPotN π (rjN P)) (nW P) m) c σ ≤ ENNReal.ofReal
        ((epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) *
          σ.trace.re) :=
    fun m hε hk ↦ readCost_le_of_keep _ c hk hσ (epsQ_nonneg nD P)
      ((keepE_le_of_portInst _ ENNReal.ofReal_ne_top c hε hσ hg).trans_eq
        (by rw [ENNReal.toReal_ofReal (epsQ_nonneg nD P)]))
  have hfin : ((rjN P : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      ((epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) *
        σ.trace.re) = ENNReal.ofReal (rjR nD P * σ.trace.re) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    unfold rjR
    exact congrArg ENNReal.ofReal (mul_assoc _ _ _).symm
  cases c with
  | readH z u =>
    exact (tsum_potential_readH_le (fun s ↦ Nat.cast_nonneg _)
      (recPotN_offCell π (rjN P) z) u hσ).trans le_self_add
  | readK x u =>
    refine (tsum_potential_read_layer_le (recPotN π (rjN P)) (nW P) nD (rjN P)
      (fun s _ _ ↦ recPotN_le π (rjN P) s) _ hσ hnb (fun m ↦ hcost m
        (fun W mm ↦ portInst_recLev_k π hπ (rjN P) (nW P) nD m W mm) hok) hsupp).trans
      (add_le_add le_rfl (le_of_eq hfin))
  | readK' x u =>
    refine (tsum_potential_read_layer_le (recPotN π (rjN P)) (nW P) nD (rjN P)
      (fun s _ _ ↦ recPotN_le π (rjN P) s) _ hσ hnb (fun m ↦ hcost m
        (fun W mm ↦ portInst_recLev_k' π hπ (rjN P) (nW P) nD m W mm) hok) hsupp).trans
      (add_le_add le_rfl (le_of_eq hfin))

open scoped Classical in
/-- **The program ports**: inside a hardwired table `Wt`, a program pays its `RecJ` weight out of
the potential, up to `rjN P` times the target-free fresh flips (`kfW`). -/
theorem recJW_add_prog_rj (d : EvData) {P T : ℕ} {Wt : Hw X Z} (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hc : ProgOf Wt c)
    (hsupp : ∀ q, σ q q ≠ 0 → Quantum.Sponge.HwLe q.2.2.1 Wt ∧
      dbGrade q.2.2.1 ≤ P ∧ P + dbGrade q.2.1 ≤ T) :
    recJW d c σ + ∑' r, potential (diagPot fun s ↦ √(recPotN d.perm (rjN P) s : ℝ))
        (MatrixMap.conj (hwProgKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(recPotN d.perm (rjN P) s : ℝ)) σ +
        (rjN P : ℝ≥0∞) * kfW d.perm P T c σ := by
  have hφ0 : ∀ s : HwReg X Z (Finset S × M'), 0 ≤ (recPotN d.perm (rjN P) s : ℝ) :=
    fun s ↦ Nat.cast_nonneg _
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hne : ∀ q : Unit × HwReg X Z (Finset S × M'), (σ q q).re ≠ 0 → σ q q ≠ 0 :=
    fun q h h0 ↦ h (by rw [h0, Complex.zero_re])
  rw [tsum_potential_prog_eq hφ0 c hσ, potential_diagPot_sqrt hφ0]
  cases c with
  | programH z y =>
    refine (ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ d (.programH z y) q.2) ∅
      (fun q ↦ (recPotN d.perm (rjN P) q.2 : ℝ))
      (fun q ↦ (recPotN d.perm (rjN P) (progMap (.programH z y) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) (rjN P) (fun _ _ h ↦ h.elim) (fun q _ _ ↦ by
        rw [recPotN_progH]) (fun q _ ↦ by
        rw [recPotN_progH]
        exact le_add_of_nonneg_right (Nat.cast_nonneg _))).trans_eq ?_
    show _ + _ * diagMass ∅ σ = _ + _ * 0
    rw [diagMass_empty]
  | programK y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ d (.programK y a) q.2)
      (kfSet d.perm P T y a) (fun q ↦ (recPotN d.perm (rjN P) q.2 : ℝ))
      (fun q ↦ (recPotN d.perm (rjN P) (progMap (.programK y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) (rjN P) (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.1 y ≠ none → q.2.2.1.2.1 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : Wt.2.1 y = some b := hW.2.1 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK_le d.perm (rjN P) y a q.2 hWa
    · exact_mod_cast recPotN_progK_add_one_le d.perm (rjN P) y a (hwKs_lt_rjN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq ⟨hF, hg1, hg2⟩, add_zero] at hle
      exact_mod_cast hle
    · have : recPotN d.perm (rjN P) (progMap (.programK y a) q.2) ≤
          recPotN d.perm (rjN P) q.2 + rjN P :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this
  | programK' y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ d (.programK' y a) q.2)
      (kfSet' d.perm P T y a) (fun q ↦ (recPotN d.perm (rjN P) q.2 : ℝ))
      (fun q ↦ (recPotN d.perm (rjN P) (progMap (.programK' y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) (rjN P) (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.2 y ≠ none → q.2.2.1.2.2 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : Wt.2.2 y = some b := hW.2.2 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK'_le d.perm (rjN P) y a q.2 hWa
    · exact_mod_cast recPotN_progK'_add_one_le d.perm (rjN P) y a (hwKs_lt_rjN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq ⟨hF, hg1, hg2⟩, add_zero] at hle
      exact_mod_cast hle
    · have : recPotN d.perm (rjN P) (progMap (.programK' y a) q.2) ≤
          recPotN d.perm (rjN P) q.2 + rjN P :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this

end ports

/-! ## The run -/

section run

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The calls of a run stay inside a hardwired table `Wt`**: a called program port programs a
cell of `Wt` with its value, and the presented operator vanishes off `HwLe · Wt` (the hypothesis
`W`, `hW`, `hxW` of EncPorts' `totalWeight_kJumpW_le`). -/
def StaysIn (m₀ : Finset S × M') (I : Λ.Interp) {A : QReg} (Wt : Hw X Z)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω A)
    (ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    Prop :=
  ∃ W : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop,
    (∀ i E σ, W i E σ → ProgPort Wt i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.1.2.2.1 Wt → σ a a = 0) ∧
    (runtimeR m₀).ForallQueries I W x ρ

/-- **The `RecJ` weight of a run**: from a basis state beside the initial register, with at most `n`
sponge, `K` classical and `P` program calls, only `EncReadOk` reads, calls inside a hardwired table
`Wt` and `P + n + K ≤ T`, at data with `PermGood π 18`, at most `rjS (n + K) P` per sponge call,
`rjR (n + K) P` per classical call and `rjN P` times the target-free fresh flips `kfW`. -/
theorem totalWeight_recJW_le (d : EvData) (hπ : PermGood d.perm 18) (m₀ : Finset S × M')
    (I : Λ.Interp) {B : Type} [Fintype B] [DecidableEq B] (u : B)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {n K P T : ℕ}
    (hT : P + (n + K) ≤ T) (Wt : Hw X Z)
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (hok : IFreeM.IsChargeBound x (portCharge (okChg (EncReadOk updOf))) 0)
    (hP : IFreeM.IsChargeBound x
      (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M'))) P)
    (hW : StaysIn m₀ I Wt x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (fun _ _ ↦ 0) (recJW d))) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      ((n : ℝ≥0∞) * ENNReal.ofReal (rjS (n + K) P) +
        (K : ℝ≥0∞) * ENNReal.ofReal (rjR (n + K) P)) +
        (rjN P : ℝ≥0∞) * (runtimeR m₀).totalWeight I
          (extWeight (hwCost (fun _ _ ↦ 0) (kfW d.perm P T))) x
          ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  obtain ⟨Q, hQ, hx⟩ := forallQueries_portInv (EncReadOk updOf) m₀ I u x hn hK hok hP
  obtain ⟨W, hWW, hxW⟩ := hW
  have hφ0 : ∀ s : HwReg X Z (Finset S × M'), 0 ≤ (recPotN d.perm (rjN P) s : ℝ) :=
    fun s ↦ Nat.cast_nonneg _
  set Kp := diagPot fun s : HwReg X Z (Finset S × M') ↦ √(recPotN d.perm (rjN P) s : ℝ) with hKp
  set wS : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re with hwS
  set wR : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0) with hwR
  set wK : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kfW d.perm P T)) with hwK
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m₀) I Kp
    (fun i E σ ↦ Q i E σ ∧ W i E σ)
    (fun i τ ↦ PortInv (EncReadOk updOf) (n + K) P m₀ i τ ∧ ProgPort Wt i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.2.2.1 Wt → τ a a = 0)
    (fun i E σ h ↦ ⟨hQ i E σ h.1, (hWW i E σ h.2).1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ (hWW i E σ h.2).2 (a, e) ha⟩)
    (extWeight (hwCost (fun _ _ ↦ 0) (recJW d)))
    (fun i σ ↦ ENNReal.ofReal (rjS (n + K) P) * wS i σ +
      (ENNReal.ofReal (rjR (n + K) P) * wR i σ + (rjN P : ℝ≥0∞) * wK i σ))
    (fun i σ hσ hI ↦ ?_) x hρ (forallQueries_and hx hxW)
  · have hgood : Good d.perm (union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) :=
      (good_congr (U := union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) (U' := emptyDbs)
        (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)).2 good_emptyDbs
    have h0 : potential Kp ρ = 0 := (potential_basis_init m₀ hφ0 u).trans (by
      rw [recPotN_of_good d.perm (rjN P) (s := ((Database.empty, Database.empty, Database.empty),
        hwEmpty X Z, m₀)) hgood, Nat.cast_zero, ENNReal.ofReal_zero])
    have e := (totalWeight_add_weight (runtimeR m₀) I
      (fun i σ ↦ ENNReal.ofReal (rjS (n + K) P) * wS i σ)
      (fun i σ ↦ ENNReal.ofReal (rjR (n + K) P) * wR i σ + (rjN P : ℝ≥0∞) * wK i σ)
      x ρ).trans (congrArg₂ (· + ·)
        (totalWeight_const_mul_weight (runtimeR m₀) I _ wS x ρ)
        ((totalWeight_add_weight (runtimeR m₀) I
          (fun i σ ↦ ENNReal.ofReal (rjR (n + K) P) * wR i σ)
          (fun i σ ↦ (rjN P : ℝ≥0∞) * wK i σ) x ρ).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wR x ρ)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wK x ρ))))
    have hS : (runtimeR m₀).totalWeight I wS x ρ ≤ (n : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m₀) I
        (fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) x hn hρ).trans
          ((mul_le_mul_of_nonneg_left (ofReal_trace_basis_init m₀ u).le zero_le).trans_eq
            (mul_one _))
    have hR : (runtimeR m₀).totalWeight I wR x ρ ≤ K :=
      (totalWeight_le_totalWeight (runtimeR m₀) I
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((p | c) | c) | T
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) x hρ).trans
        (totalWeight_calls_le_basis m₀ I u x hK)
    calc (runtimeR m₀).totalWeight I (extWeight (hwCost (fun _ _ ↦ 0) (recJW d))) x ρ
        ≤ potential Kp ρ + (runtimeR m₀).totalWeight I
          (fun i σ ↦ ENNReal.ofReal (rjS (n + K) P) * wS i σ +
            (ENNReal.ofReal (rjR (n + K) P) * wR i σ + (rjN P : ℝ≥0∞) * wK i σ)) x ρ := h
      _ = ENNReal.ofReal (rjS (n + K) P) * (runtimeR m₀).totalWeight I wS x ρ +
          (ENNReal.ofReal (rjR (n + K) P) * (runtimeR m₀).totalWeight I wR x ρ +
            (rjN P : ℝ≥0∞) * (runtimeR m₀).totalWeight I wK x ρ) := by
        rw [h0, zero_add, e]
      _ ≤ ENNReal.ofReal (rjS (n + K) P) * (n : ℝ≥0∞) +
          (ENNReal.ofReal (rjR (n + K) P) * (K : ℝ≥0∞) +
            (rjN P : ℝ≥0∞) * (runtimeR m₀).totalWeight I wK x ρ) :=
        add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (add_le_add (mul_le_mul_of_nonneg_left hR zero_le) le_rfl)
      _ = _ := by ring
  · rcases i with ((p | c) | c) | T'
    · have hb : ∀ r : Unit, ((runtimeR m₀).step (.inl (.inl (.inl p)))).branch r σ =
          MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ p r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential Kp (((runtimeR m₀).step (.inl (.inl (.inl p)))).branch r σ) ≤
        potential Kp σ + (ENNReal.ofReal (rjS (n + K) P) *
          (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (rjR (n + K) P) * 0 + (rjN P : ℝ≥0∞) * 0))
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (rjS_nonneg _ _)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
        (hS_rj (EncReadOk updOf) d.perm hπ m₀ p hσ hI.1)
    · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
          MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential Kp (((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ) ≤
        potential Kp σ + (ENNReal.ofReal (rjS (n + K) P) *
          (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (rjR (n + K) P) * ENNReal.ofReal σ.trace.re + (rjN P : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (rjR_nonneg _ _)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
        (hR_rj updOf d.perm hπ m₀ c hσ hI.1)
    · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
          MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
      show recJW d c σ + ∑' r, potential Kp (((runtimeR m₀).step (.inl (.inr c))).branch r σ) ≤
        potential Kp σ + (ENNReal.ofReal (rjS (n + K) P) *
          (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (rjR (n + K) P) * 0 + (rjN P : ℝ≥0∞) * kfW d.perm P T c σ))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
      refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r)))).trans
        (recJW_add_prog_rj d c hσ hI.2.1 fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2, ?_⟩)
      · by_contra h
        exact ha (hI.2.2 a h)
      · have h1 : dbGrade a.2.1 ≤ n + K := (hI.1.2.1 a a ha).1.1
        omega
    · show (0 : ℝ≥0∞) + ∑' r, potential Kp (((runtimeR m₀).step (.inr T')).branch r σ) ≤
        potential Kp σ + (ENNReal.ofReal (rjS (n + K) P) *
          (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (rjR (n + K) P) * 0 + (rjN P : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      exact tsum_potential_recStep_diag hφ0 (fun _ _ _ _ _ ↦ rfl) T' hσ

end run

/-! ## The challenge prefix -/

section prefixRJ

/-- **The `RecJ` weight of the challenge prefix**, at the template data `(p, v)`. -/
noncomputable def recJPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (recJW (evData p v))))
    (prefixR pol A p v) initR

/-- **The target-free fresh flips of the challenge prefix's programs**, at hardwired grade
`progCap` and grade `2^68`. -/
noncomputable def kfPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (kfW p.perm progCap (2 ^ 68)))) (prefixR pol A p v) initR

/-- The prefix's calls stay inside the hardwired table `Wt`. -/
def StaysInR (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s)
    (Wt : Hw X Z) : Prop :=
  StaysIn m0R .instruments Wt (prefixR pol A p v) initR

/-- EncPorts' port charge of `EncReadOk` for the trial update is at most CostRun's `bR`. -/
theorem okChg_encReadOk_le_bR (i : (recHwSpec X Z HPos Selections).Port) :
    okChg (EncReadOk trialUpd) i ≤ bR i := by
  rcases i with ((i | c) | c) | T
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h
  · show okChg (EncReadOk trialUpd) (.inl (.inl (.inr c))) ≤ okCharge c
    by_cases h : ReadOk c
    · rw [okCharge_eq_zero h]
      have he : EncReadOk trialUpd c := by
        rcases h with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht
        · exact fun _ _ ↦ rfl
        · exact fun _ _ ↦ rfl
        · obtain ⟨zt, rfl⟩ := ht
          exact ⟨zt, rfl⟩
      unfold okChg
      rw [ite_eq_left (show OkPort (EncReadOk trialUpd) (.inl (.inl (.inr c))) from he)]
    · unfold okChg okCharge
      rw [ite_eq_right h]
      split_ifs <;> omega
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The `RecJ` weight of the challenge prefix**: at data with `PermGood π 18`, for `q ≤ 2^64`,
with the prefix's calls inside a hardwired table, at most `rjS` per sponge call, `rjR` per
classical call and `rjN progCap` times the target-free fresh flips `kfPre`, for every digest
policy. -/
theorem recJPre_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {Wt : Hw X Z} (hW : StaysInR pol A p v Wt) :
    recJPre pol A p v ≤ ((6 * q : ℕ) * ENNReal.ofReal (rjS (6 * q + clsCap) progCap) +
      (clsCap : ℝ≥0∞) * ENNReal.ofReal (rjR (6 * q + clsCap) progCap)) +
      (rjN progCap : ℝ≥0∞) * kfPre pol A p v :=
  totalWeight_recJW_le trialUpd (evData p v) hπ m0R .instruments () (prefixR pol A p v)
    (progCap_add_le hq) Wt (advCalls_prefixR hperm hsign pol p v)
    (clsCalls_prefixR hperm hsign pol p v)
    (isChargeBound_mono_charge (fun _ a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact okChg_encReadOk_le_bR i) (chgB_prefixR pol A p v))
    (progCalls_prefixR hperm hsign pol p v) hW

/-- **The bound on the averaged `RecJ` weight** from the averaged `kfPre` bound `κ`. -/
noncomputable def recCapS (q : ℕ) (κ : ℝ≥0∞) : ℝ≥0∞ :=
  ((6 * q : ℕ) * ENNReal.ofReal (rjS (6 * q + clsCap) progCap) +
    (clsCap : ℝ≥0∞) * ENNReal.ofReal (rjR (6 * q + clsCap) progCap)) + (rjN progCap : ℝ≥0∞) * κ

/-- **The averaged `RecJ` weight of the challenge prefix**: over a finite family of template data
`(P θ, V θ)` and a good set on which `PermGood π 18` holds and the prefix's calls stay inside a
hardwired table, from the averaged bound `κ` of `kfPre`, at most `recCapS q κ`. -/
theorem uavg_recJPre_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) {Θ : Type} [Fintype Θ]
    (P : Θ → Pub) (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good]
    (hgood : ∀ θ, good θ → PermGood (P θ).perm 18 ∧ ∃ Wt, StaysInR pol A (P θ) (V θ) Wt)
    {κ : ℝ≥0∞} (hkf : uavg (fun θ ↦ if good θ then kfPre pol A (P θ) (V θ) else 0) ≤ κ) :
    uavg (fun θ ↦ if good θ then recJPre pol A (P θ) (V θ) else 0) ≤ recCapS q κ :=
  uavg_ite_le_add_mul (fun θ hθ ↦ by
    obtain ⟨hπ, Wt, hW⟩ := hgood θ hθ
    exact recJPre_le hperm hsign hq pol (P θ) (V θ) hπ hW) hkf

end prefixRJ

/-! ## The constants at Keccak's sizes -/

section keccak

set_option exponentiation.threshold 4096 in
/-- **The fresh-cell rate of the prefix**: `epsQ (6q + clsCap) progCap ≤ 2^-302` for `q ≤ 2^64`. -/
theorem epsQ_prefix_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    epsQ (6 * q + clsCap) progCap ≤ (2 ^ 302 : ℝ)⁻¹ := by
  have hT : nW progCap + (6 * q + clsCap) ≤ 2 ^ 68 + 1 := by
    have := progCap_add_le hq
    unfold nW
    omega
  have hc : capKJ (nW progCap + (6 * q + clsCap)) 18 + capKJ' (nW progCap + (6 * q + clsCap)) 18 ≤
      2 ^ 210 :=
    (Nat.add_le_add (capKJ_mono hT 18) (capKJ'_mono hT 18)).trans (by norm_num [capKJ, capKJ'])
  have hc' : ((capKJ (nW progCap + (6 * q + clsCap)) 18 +
      capKJ' (nW progCap + (6 * q + clsCap)) 18 : ℕ) : ℝ) ≤ 2 ^ 210 := by
    exact_mod_cast hc
  unfold epsQ epsLev
  rw [card_Z, div_le_iff₀ (by positivity)]
  refine hc'.trans (le_of_eq ?_)
  push_cast
  norm_num

theorem rjN_le : (rjN progCap : ℝ) ≤ 2 ^ 43 := by
  unfold rjN
  rw [progCap_eq]
  norm_num [signatureLimit]

set_option exponentiation.threshold 4096 in
/-- **The sponge charge**: `rjS ≤ 2^-104` for `q ≤ 2^64`. -/
theorem rjS_le {q : ℕ} (hq : q ≤ 2 ^ 64) : rjS (6 * q + clsCap) progCap ≤ (2 ^ 104 : ℝ)⁻¹ := by
  have he := epsQ_prefix_le hq
  have he0 := epsQ_nonneg (6 * q + clsCap) progCap
  have h6 : 6 * epsQ (6 * q + clsCap) progCap ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by
    calc 6 * epsQ (6 * q + clsCap) progCap ≤ 6 * (2 ^ 302 : ℝ)⁻¹ := by gcongr
      _ ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by norm_num
  have hs : √(6 * epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 149 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt h6).trans_eq (Real.sqrt_sq (by positivity))
  unfold rjS
  calc (rjN progCap : ℝ) * (2 * √(6 * epsQ (6 * q + clsCap) progCap) +
        6 * epsQ (6 * q + clsCap) progCap)
      ≤ 2 ^ 43 * (2 * (2 ^ 149 : ℝ)⁻¹ + ((2 ^ 149 : ℝ)⁻¹) ^ 2) := by
        gcongr
        exact rjN_le
    _ ≤ (2 ^ 104 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- **The read charge**: `rjR ≤ 2^-106` for `q ≤ 2^64`. -/
theorem rjR_le {q : ℕ} (hq : q ≤ 2 ^ 64) : rjR (6 * q + clsCap) progCap ≤ (2 ^ 106 : ℝ)⁻¹ := by
  have he := epsQ_prefix_le hq
  have he0 := epsQ_nonneg (6 * q + clsCap) progCap
  have he' : epsQ (6 * q + clsCap) progCap ≤ ((2 ^ 151 : ℝ)⁻¹) ^ 2 := he.trans_eq (by norm_num)
  have hs : √(epsQ (6 * q + clsCap) progCap) ≤ (2 ^ 151 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt he').trans_eq (Real.sqrt_sq (by positivity))
  have hX : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hZ : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_Z]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold rjR
  calc (rjN progCap : ℝ) * (epsQ (6 * q + clsCap) progCap +
        (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ (6 * q + clsCap) progCap))
      ≤ 2 ^ 43 * ((2 ^ 302 : ℝ)⁻¹ + ((2 ^ 511 : ℝ)⁻¹ + (2 ^ 511 : ℝ)⁻¹) +
        2 * (2 ^ 151 : ℝ)⁻¹) := by
        gcongr
        exact rjN_le
    _ ≤ (2 ^ 106 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- **`recCapS` at Keccak's sizes**: `recCapS q κ ≤ 2^-36 + 2^43 κ` for `q ≤ 2^64`. -/
theorem recCapS_le {q : ℕ} (hq : q ≤ 2 ^ 64) (κ : ℝ≥0∞) :
    recCapS q κ ≤ (2 ^ 36 : ℝ≥0∞)⁻¹ + 2 ^ 43 * κ := by
  have hcls : (clsCap : ℝ) ≤ 2 ^ 68 := by
    have := progCap_add_le (q := 0) (Nat.zero_le _)
    exact_mod_cast (by omega : clsCap ≤ 2 ^ 68)
  have h6q : ((6 * q : ℕ) : ℝ) ≤ 6 * 2 ^ 64 := by exact_mod_cast (by omega : 6 * q ≤ 6 * 2 ^ 64)
  have h1 : ((6 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (rjS (6 * q + clsCap) progCap) ≤
      ENNReal.ofReal (6 * 2 ^ 64 * (2 ^ 104 : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul h6q (rjS_le hq) (rjS_nonneg _ _) (by positivity))
  have h2 : (clsCap : ℝ≥0∞) * ENNReal.ofReal (rjR (6 * q + clsCap) progCap) ≤
      ENNReal.ofReal (2 ^ 68 * (2 ^ 106 : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hcls (rjR_le hq) (rjR_nonneg _ _) (by positivity))
  have h3 : (rjN progCap : ℝ≥0∞) ≤ 2 ^ 43 := by
    rw [← ENNReal.ofReal_natCast, show (2 ^ 43 : ℝ≥0∞) = ENNReal.ofReal (2 ^ 43) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal rjN_le
  unfold recCapS
  refine add_le_add ((add_le_add h1 h2).trans ?_) (mul_le_mul_of_nonneg_right h3 zero_le)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), inv_two_pow_eq_ofReal 36]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num

end keccak

end Quantum.Sphincs.Assembly

end
