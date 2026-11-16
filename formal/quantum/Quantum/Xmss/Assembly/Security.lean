module

public import Quantum.Xmss.Assembly.TableComp
public import Quantum.Xmss.Assembly.Runtime1
public import Quantum.Xmss.Assembly.Costs
public import Quantum.Xmss.Assembly.RecordPorts
public import Quantum.Xmss.Assembly.RecordDrop
public import Quantum.Xmss.Hybrid.CoinsHiding
public import Quantum.Xmss.Hybrid.Graded
public import Quantum.Xmss.EncCost
public import Quantum.Sponge.Keccak
public import Quantum.Sponge.Reads
public import VCVio.Quantum.VC.Emulated

@[expose] public section

/-!
# leanXMSS is quantum SUF-CMA secure in the QRPM, from its open debts

The assembly of the chain of games (design, sections 2 and 9). Every step is a committed theorem;
every link that the committed theorems do not provide is a field of `XmssQrpmDebts q A`, stated as
exactly the missing link. The averages are over the uniform honest table `L : HonestTable`
(keys, `π`, master seed). Steps 1 to 3 run with the inner memory `Unit`; the canonical game's
register has the memory `Mem = Finset ValPos × Selections`: the template's memory label and Events'
selections. The canonical runtime-2 game is
`gameR A L = realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)` (Template; each
randomizer trial's `h`-read records a codeword selection with EncCost's `cwUpd`), run against
`runtimeR m0R` (runtime 2 with record ports); it is also the event-bound program (CoinsEvent).

1. **G0 to runtime 1** (`winProb_eq_uavg`): `winProb_eq_runtime1` (TableComp) with the `tableLaw`
   mixture written as the average over the table.
2. **Grind-only reads** (debt `readsT`): S5's runtime 1 on `gameReads` against the same runtime
   on the grind-only game `gameReadsT Unit (pubOf L) (valueAt L) A` (GameT) with the table `Lt L`
   hardwired (`Lt L` extends `tableHw L`: debt `tableLe`).
3. **Program ports** (`p1T_eq_p1K`: `evalDistMap_runtime1_eq_spongeHardwiredReadRuntime` with
   `dropsTo_gameD`, `progsOf_tableHw`, `ProgsOf.mono`): the game `gameD Unit (pubOf L) (valueAt L) A`
   with its program calls (record ports dropped) against Kraus's runtime 1.
4. **Record ports** (`p1K_eq_p1R`: `dropRec_gameT`, `evalDistMap_runtime1R_eq`, RecordDrop): the
   canonical game against runtime 1 with record ports (`runtime1R`) is `gameD` against runtime 1.
5. **The graded hybrid** (`uavg_win_runtime1R_le_graded_total`, Graded; debts `covers`,
   `hybSponge`, `hybRead`, with `advCalls`): `runtime1R` against `runtimeR` on the canonical game,
   paying `√(4 · 6q · μ)` for the hidden mass `μ ≤ 6q κ` at the sponge ports (`κ = kappaS`) and
   `√ν` for the hidden mass `ν ≤ clsCap κ_read` at the read ports (`κ_read = kappaR`). The Disclose
   part for the 128-bit `k`-cells is `uavg_hiddenK_digest_le` (from `viewByOn_gameT`, for
   `runtimeR`).
6. **End** (debt `endReads`, with `dbGrade_le_progCap_extend`): the final reads and the
   classification (`win_imp_bad`) put a win in `BadR L progCap` (Events' `Bad` on the selections),
   up to the read error.
7. **The event bound** (`eventWeight_runtimeR_le` on `BadR L progCap`, `labelFree_badR`, with
   `freshBound_slice_bad`, `upClosed_slice_bad`, `empty_not_mem_bad` and the flip costs
   `potential_hwReadKraus_le`, `potential_hwProgKraus_le`), for `PermGood L.perm 18`.
8. **Classical costs** (`encCost_key_le` per key; debts `clsSplit`, `keyFacts`, `clsTotal`): the
   total flip cost, averaged over the good tables, is at most `clsBound q`.
9. **Permutation goodness** (`prob_not_permGood_keccak`): the bad tables weigh at most `2^-777`.

`qrpmBound q = (√eventTerm + hybTerm)²` with
`eventTerm = (∑_{n < 6q} √(6 εₙ) + √clsBound)² + readError + 2^-777` and
`hybTerm = √(4 · 6q · 6q κ) + √(clsCap κ_read)`.
-/

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Averages over a table split into three coordinates -/

section avg

variable {Θ S P K : Type*} [Fintype Θ] [Fintype S] [Fintype P] [Fintype K]

theorem uavg_const [Nonempty Θ] (c : ℝ≥0∞) : uavg (fun _ : Θ ↦ c) = c := by
  simp only [uavg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul]

theorem card_inv_of_equiv (e : Θ ≃ S × P × K) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ =
      (Fintype.card S : ℝ≥0∞)⁻¹ * ((Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) := by
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

theorem sum_of_equiv (e : Θ ≃ S × P × K) (F : Θ → ℝ≥0∞) :
    ∑ θ, F θ = ∑ s, ∑ p, ∑ k, F (e.symm (s, p, k)) := by
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

/-- **The `tableLaw` mixture is the table average.** Averaging over `s`, `p` the `tableLaw` mixture
of the data `g s p k` over uniform `k` is the uniform average over `Θ ≃ S × P × K`. -/
theorem avg_tableLaw_eq_uavg {β : Type*} [DecidableEq β] (e : Θ ≃ S × P × K)
    (g : S → P → K → β) (R : P → β → ℝ≥0∞) :
    (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ s, (Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p,
        ∑ b ∈ Finset.univ.image (g s p), tableLaw (g s p) b * R p b =
      uavg (fun θ ↦ R (e θ).2.1 (g (e θ).1 (e θ).2.1 (e θ).2.2)) := by
  have h1 : ∀ s p, ∑ b ∈ Finset.univ.image (g s p), tableLaw (g s p) b * R p b =
      ∑ k, (Fintype.card K : ℝ≥0∞)⁻¹ * R p (g s p k) := fun s p ↦ by
    simpa only [smul_eq_mul] using (sum_uniform_comp_eq_sum_tableLaw (g s p) (R p)).symm
  simp only [h1, uavg, card_inv_of_equiv e, sum_of_equiv e, Equiv.apply_symm_apply,
    Finset.mul_sum, mul_assoc]

/-- The average of a function of the middle coordinate. -/
theorem uavg_comp_snd_fst [Nonempty S] [Nonempty K] (e : Θ ≃ S × P × K) (h : P → ℝ≥0∞) :
    uavg (fun θ ↦ h (e θ).2.1) = (Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p := by
  have hS : (Fintype.card S : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uavg, card_inv_of_equiv e, sum_of_equiv e, Equiv.apply_symm_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  calc (Fintype.card S : ℝ≥0∞)⁻¹ * ((Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
        ((Fintype.card S : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞) * ∑ p, h p))
      = ((Fintype.card S : ℝ≥0∞)⁻¹ * Fintype.card S) *
          (((Fintype.card K : ℝ≥0∞)⁻¹ * Fintype.card K) *
            ((Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p)) := by ring
    _ = (Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p := by
      rw [ENNReal.inv_mul_cancel hS (ENNReal.natCast_ne_top _),
        ENNReal.inv_mul_cancel hK (ENNReal.natCast_ne_top _), one_mul, one_mul]

theorem pow_two_rpow_inv_two (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Jensen for `(a + √f)²`**: the average is at most `(a + √(E f))²`. -/
theorem uavg_sq_add_sqrt_le [Nonempty Θ] (a : ℝ≥0∞) (f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (a + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤ (a + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h4 : ∀ y : ℝ≥0∞, 4 * (4⁻¹ * y) = y := fun y ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hsingle : ∀ y : ℝ≥0∞, ∑' j : ℕ, (4 * (if j = 0 then 4⁻¹ * y else 0)) ^ (2⁻¹ : ℝ) =
      y ^ (2⁻¹ : ℝ) := fun y ↦ by
    rw [tsum_eq_single 0 fun j hj ↦ by
      simp only [hj, ↓reduceIte, mul_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
    simp only [↓reduceIte, h4]
  have h := uavg_le_of_hybrid (fun θ ↦ (a + f θ ^ (2⁻¹ : ℝ)) ^ 2) (fun _ ↦ a ^ 2)
    (fun θ j ↦ if j = 0 then 4⁻¹ * f θ else 0) fun θ ↦ by
      rw [pow_two_rpow_inv_two, pow_two_rpow_inv_two, hsingle]
  refine h.trans_eq ?_
  have hμ : ∀ j : ℕ, uavg (fun θ ↦ if j = 0 then 4⁻¹ * f θ else 0) =
      if j = 0 then 4⁻¹ * uavg f else 0 := fun j ↦ by
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte, uavg_const_mul]
    · simp only [hj, ↓reduceIte, uavg_const]
  simp only [hμ, uavg_const, pow_two_rpow_inv_two, hsingle]

end avg

/-! ## The register, the table and the game in runtime 1 -/

section game

/-- Equality of secret keys, decided classically for TableComp (not a global instance). -/
noncomputable local instance secretKeyDecEq : DecidableEq SecretKey := Classical.decEq _

/-- The memory of the runtimes: the template's label and Events' selections. -/
abbrev Mem : Type := Finset ValPos × Selections

/- Instance search for `Mem` exceeds the default size: found once here, the same term the search
would build, for every consumer of `Mem`. -/
set_option synthInstance.maxSize 1000 in
instance memDecEq : DecidableEq Mem := inferInstance

/-- No selection recorded. -/
def m0 : Selections := fun _ _ ↦ none

/-- The initial memory: nothing disclosed, nothing selected. -/
def m0R : Mem := (∅, m0)

/-- The honest table as master seed, permutation and keys. -/
def tableSplit : HonestTable ≃ MasterSeed × Equiv.Perm (X × Z) × SpongeKeys X Z :=
  tableEquiv.trans ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))

/-- The game's win bit. -/
def winObs (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) : Bool := p.2.2

/-- The win probability of S5's runtime 1 on the game's reads `gameReads`, at the table `L`. -/
noncomputable def p1S5 (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  runtime1Law Unit () A (SubState.basis ()) winObs L.perm
    (honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed)) {true}

theorem card_masterSeed_ennreal : (Fintype.card MasterSeed : ℝ≥0∞) = 2 ^ 256 := by
  rw [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat]

/-- **G0 is the table average of runtime 1** (`winProb_eq_runtime1`). -/
theorem winProb_eq_uavg (A : Adversary (X × Z)) :
    winProb keccakStateEquiv A = uavg (p1S5 A) := by
  rw [winProb_eq_runtime1 (M := Unit) () A, ← card_masterSeed_ennreal]
  exact avg_tableLaw_eq_uavg tableSplit
    (fun S0 π t ↦ honestEval t π (schemeWithHashFromSeed.keygen S0))
    (fun π b ↦ runtime1Law Unit () A (SubState.basis ()) winObs π b {true})

/-- **The canonical runtime-2 game** of the table `L` (Template): the template game at the public
data `pubOf L`, realized at the hidden values `valueAt L`, the trials' `h`-reads updating the
selections with `cwUpd`. -/
noncomputable def gameR (A : Adversary (X × Z)) (L : HonestTable) :
    QComp (recHwSpec X Z ValPos Selections) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)

/-- The initial state of the runtimes with record ports, beside the adversary's trivial register. -/
noncomputable def initR : Matrix (QReg.of Unit × QReg.of (HwReg X Z Mem))
    (QReg.of Unit × QReg.of (HwReg X Z Mem)) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix

end game

/-! ## The quantities of the chain -/

section quantities

/-- **Events' `Bad` on the register with the memory label**: the label is ignored. -/
def BadR (L : HonestTable) (N : ℕ) : Set (HwReg X Z Mem) :=
  {r | (r.1, r.2.1, r.2.2.2) ∈ Bad L N}

/-- Membership in `BadR`, decided classically. -/
noncomputable local instance badRDec (L : HonestTable) (N : ℕ) : DecidablePred (· ∈ BadR L N) :=
  fun _ ↦ Classical.propDecidable _

/-- S5's runtime 1 with the cells `Lt L` hardwired, running the grind-only game. -/
noncomputable def p1T (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (spongeHardwiredReadRuntime X Z (Lt L) ()).evalDistMap .instruments
    (gameReadsT Unit (pubOf L) (valueAt L) A) (SubState.basis ()) winObs {true}

/-- Kraus's runtime 1 (`Lt L` hardwired, program ports) running the canonical game with its record
ports dropped. -/
noncomputable def p1K (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime1 X Z (Lt L) ()).evalDistMap .instruments (gameD Unit (pubOf L) (valueAt L) A)
    (SubState.basis ()) winObs {true}

/-- Runtime 1 with record ports running the canonical game. -/
noncomputable def p1R (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime1R X Z (Lt L) m0R).evalDistMap .instruments (gameR A L) (SubState.basis ()) winObs
    {true}

/-- Runtime 2 with the coin table `Lc L` and record ports, running the canonical game. -/
noncomputable def p2CR (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime2CoinsR X Z (Lc L) m0R).evalDistMap .instruments (gameR A L) (SubState.basis ())
    winObs {true}

/-- `runtimeR` running `x2 L`. -/
noncomputable def p2R
    (x2 : HonestTable → QComp (recHwSpec X Z ValPos Selections) (QReg.of Unit) (QReg.of Unit)
      Bool)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).evalDistMap .instruments (x2 L) (SubState.basis ()) winObs {true}

/-- The weight of the event `BadR L progCap` at the end of the run of `x2 L` in `runtimeR`. -/
noncomputable def ewR
    (x2 : HonestTable → QComp (recHwSpec X Z ValPos Selections) (QReg.of Unit) (QReg.of Unit)
      Bool)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (x2 L) initR

/-- The flip cost of the read ports, relative to the projectors `PR L`. -/
noncomputable def dRof (PR : HonestTable → HwRead X Z Mem →
    Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) (L : HonestTable)
    (c : HwRead X Z Mem) (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    ℝ≥0∞ :=
  flipCost (BadR L progCap) (hwReadKraus c) (PR L c) σ

/-- The flip cost of the program ports, relative to the projectors `PP L`. -/
noncomputable def dPof (PP : HonestTable → HwProg X Z →
    Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) (L : HonestTable)
    (c : HwProg X Z) (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  flipCost (BadR L progCap) (hwProgKraus c) (PP L c) σ

/-- The total classical (flip) cost of the run of `x2 L` in `runtimeR` (record ports: `0`). -/
noncomputable def twR
    (x2 : HonestTable → QComp (recHwSpec X Z ValPos Selections) (QReg.of Unit) (QReg.of Unit)
      Bool)
    (PR : HonestTable → HwRead X Z Mem → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (PP : HonestTable → HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (dRof PR L) (dPof PP L))) (x2 L)
    initR

/-- The cost of the selecting reads of one key, as in `encCost_key_le`. -/
noncomputable def keyCost (J : ℕ) (p E : ℕ → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
    2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ))

/-- The bound of `encCost_key_le` on one key's cost. -/
noncomputable def keyBound (J : ℕ) (C : ℝ) (w p : ℕ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((√(C * (2 ^ 128)⁻¹ / rhoCw *
      (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2) +
    √(∑ j ∈ Finset.range J, p j)) ^ 2)

end quantities

/-! ## Runtime 2 with record ports, for a general label and memory -/

section generic

variable {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M']

/-- The program charge of runtime 2 with record ports. -/
abbrev progChargeR (S M' : Type) [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] :=
  portCharge (L := LocalSig.instruments.{0})
    (extProgCharge X Z (Finset S × M') (recSpec S M'))

/-- **The hardwired-cell cap at the end of a run of `runtimeR`**: every branch is supported on
`dbGrade W ≤ progCap`. -/
def GradeCap (m₀ : Finset S × M')
    (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool) : Prop :=
  ∀ pr : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u,
    QuerySupportedOn (fun s : pr.1 × HwReg X Z (Finset S × M') ↦ dbGrade s.2.2.1)
      (Set.Iic progCap) (((runtimeR m₀).run .instruments x).branch pr
        ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix))

/-- A record port keeps the hardwired cells, hence their grade. -/
theorem querySupportedOn_recStep_hw (T : Finset S) (r : Finset S × M') (n : ℕ)
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.2.1)
      (Set.Iic n) σ) :
    QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.2.1)
      (Set.Iic n) ((recStep (X := X) (Z := Z) T).branch r σ) := by
  rw [recStep_branch]
  exact querySupportedOn_conj_of_hw_eq (fun _ _ _ _ h ↦ by rw [eq_of_recKraus_ne_zero h]) hσ

/-- `dbGrade_le_progCap_extend` at the record ports. -/
theorem gradeCap_of (m₀ : Finset S × M')
    {x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool} {K : ℕ}
    (hx : IPFunctor.IFreeM.IsChargeBound x (progChargeR S M') K) (hK : K ≤ progCap) :
    GradeCap m₀ x :=
  fun pr ↦ dbGrade_le_progCap_extend m₀ recStep
    (fun T r n σ hσ ↦ querySupportedOn_recStep_hw T r n σ hσ) .instruments hx hK
    (SubState.basis ()) pr

/-- **Hidden `k`-cells naming one 128-bit value, for `runtimeR`, averaged over a reparametrized
table** (`sum_queryWeight_hiddenK_digest_extend_le`, `avg_le_of_sum_le`). -/
theorem uavg_hiddenK_digest_runtimeR_le {Θ P : Type} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × (S → Digest)) (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset S)
    (x : P → (S → Digest) → QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) (j : ℕ)
    (hview : ∀ p, ViewByOn (D := fun _ : S ↦ Digest) (runtimeR m₀) .instruments
      (fun i ↦ i.isLeft = true) lab (x p)
      (fun _ ↦ ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j)
    (Hk : P → (S → Digest) → Set X) (src : P → X → HwReg X Z (Finset S × M') → S)
    (val : P → X → HwReg X Z (Finset S × M') → Digest)
    (hk : ∀ p v y r, y ∈ Hk p v → r.2.1.2.1 y = none →
      src p y r ∉ lab r ∧ v (src p y r) = val p y r) :
    uavg (fun θ ↦ (runtimeR m₀).queryWeight .instruments
      (extWeight (hiddenMass ∅ (Hk (e θ).1 (e θ).2) ∅)) (x (e θ).1 (e θ).2)
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine avg_le_of_sum_le e _ _ fun p ↦ ?_
  simp only [Equiv.apply_symm_apply]
  have hρ : ENNReal.ofReal (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).trace.re ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).trace_re_le_one
  refine (sum_queryWeight_hiddenK_digest_extend_le .instruments m₀ recStep lab (x p)
    (fun _ ↦ ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)
    (fun _ ↦ (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef) j
    (fun i ↦ i.isLeft = true) (fun _ ↦ rfl) (hview p) (Hk p) (src p) (val p) (hk p)).trans ?_
  gcongr
  calc ∑ _v : S → Digest,
        ENNReal.ofReal (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).trace.re
      ≤ ∑ _v : S → Digest, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ ↦ hρ
    _ = Fintype.card (S → Digest) := by simp

end generic

/-! ## The bound -/

/-- **The classical-call cap**: three reads per block of every signing request and of the
verification (Costs: `signBlocks`, `verifyBlocks`), the program calls (`progCap`) and one record
call per program call. -/
def clsCap : ℕ := 3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap

/-- The fresh bound of the `n`-th adversary call: S4's `preimageRateBound` below
`progCap + n + clsCap + 1` entries, for `PermGood π 18`, with `2^960` values per digest. -/
noncomputable def advEps (n : ℕ) : ℝ≥0∞ :=
  preimageRateBound (X := X) (Z := Z) (progCap + (n + clsCap + 1)) 18 (2 ^ 960)

/-- The adversary term of the event bound: `∑_{n < 6q} √(6 εₙ)`. -/
noncomputable def advTerm (q : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (6 * q), (6 * advEps n) ^ (2⁻¹ : ℝ)

/-- The target of the classical costs (selecting reads, programs): `(6q + clsCap) 2^-100`. -/
noncomputable def clsBound (q : ℕ) : ℝ≥0∞ :=
  ((6 * q + clsCap : ℕ) : ℝ≥0∞) * (2 ^ 100 : ℝ≥0∞)⁻¹

/-- The read error of verification's final reads (`verifyBlocks` reads of each function). -/
noncomputable def readTerm : ℝ≥0∞ :=
  ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks)

/-- The weight of the permutations that are not `PermGood π 18`. -/
noncomputable def permTerm : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 777)

/-- The bound on runtime 2's win probability. -/
noncomputable def eventTerm (q : ℕ) : ℝ≥0∞ :=
  (advTerm q + clsBound q ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + permTerm

/-- The target per sponge call of the hidden mass at the sponge ports: `2^-128 + 2^-200` (a 128-bit
honest value, plus the capacity-scale and seed-hiding terms). -/
noncomputable def kappaS : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 200 : ℝ≥0∞)⁻¹

/-- The target per classical call of the hidden mass at the read ports: `2^-300` (to be justified
by Disclose at the read ports). -/
noncomputable def kappaR : ℝ≥0∞ :=
  (2 ^ 300 : ℝ≥0∞)⁻¹

/-- The target of the graded hidden-cell hybrid: `√(4 · 6q · μ) + √ν` with the sponge-port mass
`μ = 6q κ` over at most `6q` sponge calls and the read-port mass `ν = clsCap κ_read`. -/
noncomputable def hybTerm (q : ℕ) : ℝ≥0∞ :=
  (4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS))) ^ (2⁻¹ : ℝ) +
    ((clsCap : ℝ≥0∞) * kappaR) ^ (2⁻¹ : ℝ)

/-- **The leanXMSS QRPM bound**: `(√eventTerm + hybTerm)²`. -/
noncomputable def qrpmBound (q : ℕ) : ℝ≥0∞ :=
  (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2

/-! ## The debts -/

section debts

attribute [local instance] badRDec

/-- **The open debts of the leanXMSS QRPM proof**, for an adversary `A` making at most `q`
permutation calls. Data: runtime 1's table `Lt`, the hidden sets `H` (honest values and the
seed-keyed cells), the projectors of the flip costs, and the per-key data of the selecting reads.
The event-bound program is the canonical game `gameR A` (CoinsEvent). -/
structure XmssQrpmDebts (q : ℕ) (A : Adversary (X × Z)) where
  /-- Runtime 1's hardwired table (GameT's `tableHw L`, possibly extended). -/
  Lt : HonestTable → Hw X Z
  /-- **GameT**: runtime 1's table contains the cells the game programs, with their values. -/
  tableLe : ∀ L, HwLe (tableHw L) (Lt L)
  Hh : HonestTable → Set Z
  Hk : HonestTable → Set X
  Hk' : HonestTable → Set X
  /-- The projectors of the read ports' flip costs (FlipCost's `readPs`). -/
  PR : HonestTable → HwRead X Z Mem → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ
  /-- The projectors of the program ports' flip costs (`0` in FlipCost). -/
  PP : HonestTable → HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ
  /-- Per key: the number of selecting trials, the bound on `msgCwCount`, the unselected weights,
  the selection-read weights, the rest weights and the Enc terms of `encCost_key_le`. -/
  J : HonestTable → Layer × KeyIndex → ℕ
  C : HonestTable → Layer × KeyIndex → ℝ
  w : HonestTable → Layer × KeyIndex → ℕ → ℝ
  e : HonestTable → Layer × KeyIndex → ℕ → ℝ
  p : HonestTable → Layer × KeyIndex → ℕ → ℝ
  E : HonestTable → Layer × KeyIndex → ℕ → ℝ
  /-- The classical costs other than the selecting reads (non-selected trials, programs). -/
  rest : HonestTable → ℝ≥0∞
  /-- **GameT**: S5's runtime 1 on `gameReads` is at most (by lazy sampling over the table, equal
  to) S5's runtime 1 on the grind-only game. -/
  readsT : uavg (p1S5 A) ≤ uavg (p1T A Lt)
  /-- **Template/Reparam**: the hidden sets cover runtime 1's table (the seed-keyed cells inside). -/
  covers : ∀ L, Covers (Lt L) (Hh L) (Hk L) (Hk' L)
  /-- **The graded hybrid, sponge ports** (Disclose with `viewByOn_gameT`, Seed, CoinStage,
  CoinPath): the hidden mass at the sponge ports, summed over the calls, averaged over the table. -/
  hybSponge : uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments
    (spongeMass (Hh L) (Hk L) (Hk' L)) (gameR A L) initR) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS
  /-- **The graded hybrid, read ports** (Disclose at the read ports): the hidden mass at the read
  ports, summed over the calls, averaged over the table. -/
  hybRead : uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments
    (readMass (Hh L) (Hk L) (Hk' L)) (gameR A L) initR) ≤ (clsCap : ℝ≥0∞) * kappaR
  /-- **End**: on runs whose final hardwired cells are at most `progCap`, the final reads and the
  classification `win_imp_bad` bound the win by the event `BadR L progCap` plus the read error. -/
  endReads : ∀ L, GradeCap m0R (gameR A L) → p2R (gameR A) L ≤ ewR (gameR A) L + readTerm
  /-- **Simulation**: the canonical game makes at most `6q` sponge calls. -/
  advCalls : ∀ L, IPFunctor.IFreeM.IsChargeBound (gameR A L)
    (portCharge fun i ↦ if extCls X Z Mem (recSpec ValPos Selections) i then 0 else 1) (6 * q)
  /-- **Costs**: at most `clsCap` classical calls (reads, programs, records). -/
  clsCalls : ∀ L, IPFunctor.IFreeM.IsChargeBound (gameR A L)
    (portCharge fun i ↦ if extCls X Z Mem (recSpec ValPos Selections) i then 1 else 0) clsCap
  /-- **Costs/Template**: at most `progCap` program calls. -/
  progCalls : ∀ L, IPFunctor.IFreeM.IsChargeBound (gameR A L) (progChargeR ValPos Selections)
    progCap
  PR_proj : ∀ L c, (PR L c)ᴴ = PR L c ∧ PR L c * PR L c = PR L c
  PP_proj : ∀ L c, (PP L c)ᴴ = PP L c ∧ PP L c * PP L c = PP L c
  /-- **FlipCost/EncCost**: on good tables the total flip cost splits into the selecting reads of
  each key and the rest. -/
  clsSplit : ∀ L, PermGood L.perm 18 → twR (gameR A) PR PP L ≤
    ∑ k, keyCost (J L k) (p L k) (E L k) + rest L
  /-- **EncCost**: the per-trial facts of each key (`survive_*`, `selectReadCwE_le`). -/
  keyFacts : ∀ L, PermGood L.perm 18 → ∀ k, 0 ≤ C L k ∧ (∀ j, 0 ≤ w L k j) ∧
    (∀ j, 0 ≤ e L k j) ∧ (∀ j, 0 ≤ p L k j) ∧ (∀ j, 0 ≤ E L k j) ∧
    (∀ j < J L k, w L k (j + 1) ≤ w L k j - rhoCw * e L k j + p L k j +
      2 * √(rhoCw * e L k j * p L k j)) ∧
    (∀ j < J L k, E L k j ≤ C L k * (2 ^ 128)⁻¹ * e L k j)
  /-- **EncCost**: the average over the good tables of the keys' bounds and the rest. -/
  clsTotal : uavg (fun L ↦ if PermGood L.perm 18 then
    ∑ k, keyBound (J L k) (C L k) (w L k) (p L k) + rest L else 0) ≤ clsBound q

end debts

/-! ## The proof -/

section proof

attribute [local instance] badRDec

theorem card_Z : Fintype.card Z = 2 ^ 512 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem advEps_ne_top (n : ℕ) : advEps n ≠ ⊤ := by
  have hX : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold advEps preimageRateBound
  exact max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hX)
    (max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ))

/-- `BadR` does not read the memory label. -/
theorem labelFree_badR (L : HonestTable) (N : ℕ) : LabelFree X Z ValPos Selections (BadR L N) :=
  fun _ _ _ _ _ ↦ Iff.rfl

/-- The permutations that are not `PermGood π 18` weigh at most `2^-777` among the tables. -/
theorem uavg_not_permGood_le :
    uavg (fun L : HonestTable ↦ if PermGood L.perm 18 then 0 else 1) ≤ permTerm := by
  refine (uavg_comp_snd_fst tableSplit
    (fun π : Equiv.Perm (X × Z) ↦ if PermGood π 18 then (0 : ℝ≥0∞) else 1)).trans_le ?_
  have h := ENNReal.ofReal_le_ofReal (prob_not_permGood_keccak (X := X) (Z := Z) card_X card_Z)
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast] at h
  have hs : ∑ π : Equiv.Perm (X × Z), (if PermGood π 18 then (0 : ℝ≥0∞) else 1) =
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) := by
    rw [← Finset.sum_boole]
    exact Finset.sum_congr rfl fun π _ ↦ by by_cases hπ : PermGood π 18 <;> simp [hπ]
  rw [hs, mul_comm, ← div_eq_mul_inv]
  exact h

/-- **The program ports drop** (`dropsTo_gameD`): Kraus's runtime 1 on `gameD` is S5's runtime 1
on the grind-only game. -/
theorem p1T_eq_p1K (A : Adversary (X × Z)) {Lt : HonestTable → Hw X Z}
    (hLt : ∀ L, HwLe (tableHw L) (Lt L)) (L : HonestTable) : p1T A Lt L = p1K A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (Lt L) ()
      (dropsTo_gameD (M := Unit) ((progsOf_tableHw L).mono (hLt L)) A) (SubState.basis ())
      winObs)).symm

/-- **The record ports drop** (`dropRec_gameT`, `evalDistMap_runtime1R_eq`): runtime 1 with record
ports on the canonical game is Kraus's runtime 1 on `gameD`. -/
theorem p1K_eq_p1R (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    p1K A Lt L = p1R A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1R_eq (Lt L) m0R (dropRec_gameT cwUpd (valueAt L) (pubOf L) A)
      (SubState.basis ()) winObs)).symm

variable {q : ℕ} {A : Adversary (X × Z)}

/-- **The graded hybrid with record ports**, averaged over the table. -/
theorem uavg_p1R_le (d : XmssQrpmDebts q A) :
    uavg (p1R A d.Lt) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := by
  refine (uavg_win_runtime1R_le_graded_total .instruments d.Lt d.Hh d.Hk d.Hk' d.covers m0R
    (gameR A) (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs) (measurableSet_singleton true) (6 * q)
    d.advCalls _ _ d.hybSponge d.hybRead).trans_eq ?_
  rw [hybTerm, add_assoc]
  rfl

/-- S4's fresh bound for the slices of `BadR` (those of `Bad`, the label ignored). -/
theorem freshBound_slice_badR (L : HonestTable) (hπ : PermGood L.perm 18) (T : ℕ) (W : Hw X Z)
    (m : Mem) :
    FreshBound (slice (BadR L progCap) W m) T
      (preimageRateBound (X := X) (Z := Z) (progCap + T) 18 (2 ^ 960)) := by
  have : DecidablePred (· ∈ Bad L progCap) := fun _ ↦ Classical.propDecidable _
  convert freshBound_slice_bad (N := progCap) hπ T W m.2 using 1
  · ext D
    exact Iff.rfl

/-- **The event bound** at a good table. -/
theorem ewR_le (d : XmssQrpmDebts q A) (L : HonestTable) (hπ : PermGood L.perm 18) :
    ewR (gameR A) L ≤ (advTerm q + twR (gameR A) d.PR d.PP L ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := 6 * q) (K := clsCap) (BadR L progCap) (labelFree_badR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (empty_not_mem_bad m0) advEps
    (fun n _ ↦ advEps_ne_top n)
    (fun n _ W m ↦ freshBound_slice_badR L hπ (n + clsCap + 1) W m)
    (dRof d.PR L) (dPof d.PP L)
    (fun c σ hσ ↦ potential_hwReadKraus_le (BadR L progCap) (d.PR L)
      (fun c ↦ (d.PR_proj L c).1) (fun c ↦ (d.PR_proj L c).2) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR L progCap) (d.PP L)
      (fun c ↦ (d.PP_proj L c).1) (fun c ↦ (d.PP_proj L c).2) c σ hσ)
    .instruments (gameR A L) (d.advCalls L) (d.clsCalls L) (SubState.basis ())

/-- **The classical costs** at a good table, through `encCost_key_le`. -/
theorem twR_le (d : XmssQrpmDebts q A) (L : HonestTable) (hπ : PermGood L.perm 18) :
    twR (gameR A) d.PR d.PP L ≤
      ∑ k, keyBound (d.J L k) (d.C L k) (d.w L k) (d.p L k) + d.rest L := by
  refine (d.clsSplit L hπ).trans (add_le_add (Finset.sum_le_sum fun k _ ↦ ?_) le_rfl)
  obtain ⟨hC, hw, he, hp, hE0, hrec, hE⟩ := d.keyFacts L hπ k
  exact encCost_key_le hC (d.w L k) (d.e L k) (d.p L k) (d.E L k) hw he hp hE0 hrec hE

/-- **Runtime 2's win probability**, averaged over the table. -/
theorem uavg_p2R_le (d : XmssQrpmDebts q A) : uavg (p2R (gameR A)) ≤ eventTerm q := by
  set twg : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then twR (gameR A) d.PR d.PP L else 0
  set bad : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then 0 else 1
  have hpt : ∀ L, p2R (gameR A) L ≤ (advTerm q + twg L ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + bad L := by
    intro L
    by_cases hπ : PermGood L.perm 18
    · have hg := gradeCap_of m0R (d.progCalls L) le_rfl
      have h := (d.endReads L hg).trans (add_le_add (ewR_le d L hπ) le_rfl)
      simp only [twg, bad, hπ, ↓reduceIte, add_zero]
      exact h
    · simp only [bad, hπ, ↓reduceIte]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have htw : uavg twg ≤ clsBound q := by
    refine (uavg_mono fun L ↦ ?_).trans d.clsTotal
    by_cases hπ : PermGood L.perm 18
    · simp only [twg, hπ, ↓reduceIte]
      exact twR_le d L hπ
    · simp only [twg, hπ, ↓reduceIte, le_refl]
  calc uavg (p2R (gameR A))
      ≤ uavg (fun L ↦ (advTerm q + twg L ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + bad L) := uavg_mono hpt
    _ = uavg (fun L ↦ (advTerm q + twg L ^ (2⁻¹ : ℝ)) ^ 2) + readTerm + uavg bad := by
      rw [uavg_add, uavg_add, uavg_const]
    _ ≤ (advTerm q + uavg twg ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + permTerm := by
      gcongr
      · exact uavg_sq_add_sqrt_le _ _
      · exact uavg_not_permGood_le
    _ ≤ eventTerm q := by
      unfold eventTerm
      gcongr

/-- **The leanXMSS bound for one adversary**, from its debts. -/
theorem winProb_le_qrpmBound (d : XmssQrpmDebts q A) :
    winProb keccakStateEquiv A ≤ qrpmBound q := by
  have hK : uavg (p1T A d.Lt) = uavg (p1R A d.Lt) :=
    congrArg uavg (funext fun L ↦ (p1T_eq_p1K A d.tableLe L).trans (p1K_eq_p1R A d.Lt L))
  calc winProb keccakStateEquiv A = uavg (p1S5 A) := winProb_eq_uavg A
    _ ≤ uavg (p1T A d.Lt) := d.readsT
    _ = uavg (p1R A d.Lt) := hK
    _ ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := uavg_p1R_le d
    _ ≤ (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := by
      gcongr
      exact uavg_p2R_le d

/-- **leanXMSS is quantum SUF-CMA secure in the QRPM** with bound `qrpmBound`, given the open
debts of every adversary within the budgets. Conditional: the unconditional theorem constructs the
debts. -/
theorem leanXmss_qrpm_security_of_debts
    (hd : ∀ q (A : Adversary (X × Z)),
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q) →
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) →
      XmssQrpmDebts q A) :
    QuantumStronglyUnforgeable keccakStateEquiv qrpmBound :=
  fun q A hq hs ↦ winProb_le_qrpmBound (hd q A hq hs)

end proof

/-! ## The Disclose part of the hybrid sum -/

section disclose

/-- **The 128-bit hidden `k`-cells of the canonical game, per call** (Disclose with
`viewByOn_gameT`, through `uavg_hiddenK_digest_runtimeR_le`). For a reparametrization
`e : HonestTable ≃ P × (ValPos → Digest)` of the table into public data and the hidden honest
values, and hidden `k`-cells `HkV p v` each naming an undisclosed position whose value it carries,
the hidden mass of the `j`-th call of the realized template game against `runtimeR`, averaged over
the table, is at most `2^-128`. -/
theorem uavg_hiddenK_digest_le {P : Type} [Fintype P] (A : Adversary (X × Z))
    (e : HonestTable ≃ P × (ValPos → Digest)) (pubP : P → Pub)
    (HkV : P → (ValPos → Digest) → Set X) (src : P → X → HwReg X Z Mem → ValPos)
    (val : P → X → HwReg X Z Mem → Digest)
    (hk : ∀ p v y r, y ∈ HkV p v → r.2.1.2.1 y = none →
      src p y r ∉ r.2.2.1 ∧ v (src p y r) = val p y r) (j : ℕ) :
    uavg (fun L ↦ (runtimeR m0R).queryWeight .instruments
      (extWeight (hiddenMass ∅ (HkV (e L).1 (e L).2) ∅))
      (realizeT (e L).2 (gameT Selections cwUpd (pubP (e L).1) A)) initR j) ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  uavg_hiddenK_digest_runtimeR_le e m0R (fun r ↦ r.2.2.1)
    (fun p v ↦ realizeT v (gameT Selections cwUpd (pubP p) A)) (SubState.basis ()) j
    (fun p ↦ viewByOn_gameT Selections cwUpd (pubP p) A m0R initR j) HkV src val hk

end disclose

end Quantum.Xmss.Assembly

end
