module

public import Quantum.Xmss.Assembly.FullTable
public import Quantum.Xmss.Assembly.Runtime1
public import Quantum.Xmss.Assembly.Costs
public import Quantum.Xmss.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.RecordPorts
public import Quantum.Xmss.Assembly.RecordDrop
public import Quantum.Xmss.Assembly.CostLift
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
register has the memory `Mem = Finset HPos × Selections`: the template's memory label and Events'
selections. The canonical runtime-2 game is
`gameR A L = realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)` (Template; each
randomizer trial's `h`-read records a codeword selection with EncCost's `cwUpd`), run against
`runtimeR m0R` (runtime 2 with record ports); it is the event-bound program. It is its challenge
prefix `prefixR A L = realizeT (valueAt L) (prefixT Selections cwUpd (pubOf L) A)` followed by the
verification (`gameR_eq`, Template's `gameT_eq_prefixT_bind`).

1. **G0 to runtime 1 with the full table** (FullTable's `winProb_eq_uavg_full`): G0 is the table
   average of runtime 1 with the full honest table `fullHw L` hardwired, running the grind-only game
   `gameReadsT Unit (pubOf L) (valueAt L) A` (GameT); `fullHw L` extends `tableHw L`
   (`tableLe_fullHw`).
2. **Program ports** (`p1T_eq_p1K`: `evalDistMap_runtime1_eq_spongeHardwiredReadRuntime` with
   `dropsTo_gameD`, `progsOf_tableHw`, `ProgsOf.mono`): the game `gameD Unit (pubOf L) (valueAt L) A`
   with its program calls (record ports dropped) against Kraus's runtime 1.
3. **Record ports** (`p1K_eq_p1R`: `dropRec_gameT`, `evalDistMap_runtime1R_eq`, RecordDrop): the
   canonical game against runtime 1 with record ports (`runtime1R`) is `gameD` against runtime 1.
4. **The graded hybrid** (`uavg_win_runtime1R_le_graded_total`, Graded; debts `covers`,
   `hybSponge`, `hybRead`, with `advCalls_gameR`): `runtime1R` against `runtimeR` on the canonical
   game, paying `√(4 · 6q · μ)` for the hidden mass `μ ≤ 6q κ` at the sponge ports (`κ = kappaS`) and
   `√ν` for the hidden mass `ν ≤ clsCap κ_read` at the read ports (`κ_read = kappaR`). The Disclose
   part for the 128-bit `k`-cells is `uavg_hiddenK_digest_le` (from `viewByOn_gameT`, for
   `runtimeR`).
5. **End** (debt `endReads`, with `dbGrade_le_progCap_extend` and `progCalls_gameR`): the
   verification's reads are the final reads; with the classification (`win_imp_bad`) they put a win
   of `gameR A` in the event `BadR L progCap` (Events' `Bad` on the selections) at the end of the
   game, up to the read error `readTerm` (EndReads' `endReads_of_winDecomp`).
6. **The event bound** (`eventWeight_runtimeR_le` on `BadR L progCap` at the end of `gameR A`,
   `labelFree_badR`, with `freshBound_slice_bad`, `upClosed_slice_bad`, `empty_not_mem_bad` and the
   flip costs `potential_hwReadKraus_le`, `potential_hwProgKraus_le`), for `PermGood L.perm 18`.
   The game's call counts are GameTCalls' (`advCalls_gameR`, `clsCalls_gameR`, `progCalls_gameR`
   from the adversary's budgets); the prefix's follow by `isChargeBound_of_bind₂`
   (`advCalls_prefixR`, `clsCalls_prefixR`).
7. **Classical costs** along the game (CostLift: `flipCost_le_ports`, `totalWeight_le_lin`,
   `le_sq_add_of_forall_lin`; debts `encJoint`, `restMass`, `readEps`, `verifEpsBound`, `callsW`,
   `progRest`): the read projectors are CostLift's `PRm` (the selection reads of each randomizer
   trial's `h`-read, the empty read cell on the other read ports), the program projectors `0`.
   Along the run of the game the total flip cost is at most `(√encEpsTot + √massTot)² + progTot`:
   the codeword flips of all trials of all keys (state-weighted, at most `2^-128 cntTot`) with the
   flip terms `ε, ε'` of the other reads, the recorded mass of the reads and the programs. With the
   joint count `cntTot ≤ 2^22 (6q + progCap)`, the `k`, `k'` read flip terms per unit of the
   trace-weighted call count `callTot ≤ clsCap` (CostRun) plus the verification's `h`-read flip
   terms `verifEps` (averaged: `verifCap`, a placeholder awaiting the refined read cost), the
   recorded mass and the programs averaged, the total, averaged over the good tables, is at most
   `clsBound q` (Jensen for `(√f + √g)²`, `uavg_sqrt_add_sqrt_sq_le`).
8. **Permutation goodness** (`prob_not_permGood_keccak`): the bad tables weigh at most `2^-777`.

`qrpmBound q = (√eventTerm + hybTerm)²` with
`eventTerm = (∑_{n < 6q} √(6 εₙ) + √clsBound)² + readError + 2^-777` and
`hybTerm = √(4 · 6q · 6q κ) + √(clsCap κ_read)`. For `q > 2^64` the bound is at least `1`
(`one_le_qrpmBound`), so the debts are needed only for `q ≤ 2^64`.
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

/-- **Jensen for `(√g + √f)²`**: the average is at most `(√(E g) + √(E f))²`. -/
theorem uavg_sqrt_add_sqrt_sq_le [Nonempty Θ] (g f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (uavg g ^ (2⁻¹ : ℝ) + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h4 : ∀ y : ℝ≥0∞, 4 * (4⁻¹ * y) = y := fun y ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hsingle : ∀ y : ℝ≥0∞, ∑' j : ℕ, (4 * (if j = 0 then 4⁻¹ * y else 0)) ^ (2⁻¹ : ℝ) =
      y ^ (2⁻¹ : ℝ) := fun y ↦ by
    rw [tsum_eq_single 0 fun j hj ↦ by
      simp only [hj, ↓reduceIte, mul_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
    simp only [↓reduceIte, h4]
  have h := uavg_le_of_hybrid (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) g
    (fun θ j ↦ if j = 0 then 4⁻¹ * f θ else 0) fun θ ↦ by
      rw [pow_two_rpow_inv_two, hsingle]
  refine h.trans_eq ?_
  have hμ : ∀ j : ℕ, uavg (fun θ ↦ if j = 0 then 4⁻¹ * f θ else 0) =
      if j = 0 then 4⁻¹ * uavg f else 0 := fun j ↦ by
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte, uavg_const_mul]
    · simp only [hj, ↓reduceIte, uavg_const]
  simp only [hμ, hsingle]

/-- **Jensen for `(a + √f)²`**: the average is at most `(a + √(E f))²`. -/
theorem uavg_sq_add_sqrt_le [Nonempty Θ] (a : ℝ≥0∞) (f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (a + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤ (a + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := uavg_sqrt_add_sqrt_sq_le (fun _ : Θ ↦ a ^ 2) f
  rwa [uavg_const, pow_two_rpow_inv_two] at h

end avg

/-! ## The register, the table and the game in runtime 1 -/

section game

/-- The memory of the runtimes: the template's label and Events' selections. -/
abbrev Mem : Type := Finset HPos × Selections

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

/-- **The canonical runtime-2 game** of the table `L` (Template): the template game at the public
data `pubOf L`, realized at the hidden values `valueAt L`, the trials' `h`-reads updating the
selections with `cwUpd`. -/
noncomputable def gameR (A : Adversary (X × Z)) (L : HonestTable) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)

/-- **The challenge prefix of the canonical game**, the event-bound program: Template's `prefixT`
at `pubOf L`, realized at `valueAt L`. -/
noncomputable def prefixR (A : Adversary (X × Z)) (L : HonestTable) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SignLog)) :=
  realizeT (valueAt L) (prefixT Selections cwUpd (pubOf L) A)

/-- **The canonical game is its challenge prefix, then the verification.** -/
theorem gameR_eq (A : Adversary (X × Z)) (L : HonestTable) :
    gameR A L =
      (prefixR A L).bind fun x ↦ realizeT (valueAt L) (verifyT Selections (pubOf L) x) :=
  (congrArg (realizeT (valueAt L)) (gameT_eq_prefixT_bind Selections cwUpd (pubOf L) A)).trans
    (realizeT_bind₂ _ _ _)

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
    (x2 : HonestTable → QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      Bool)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).evalDistMap .instruments (x2 L) (SubState.basis ()) winObs {true}

/-- The weight of the event `BadR L progCap` at the end of the run of `x2 L` in `runtimeR`
(canonically the game `gameR A`). -/
noncomputable def ewR {α : Type}
    (x2 : HonestTable → QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) α)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (x2 L) initR

/-- The memory update of a randomizer trial's `h`-read on `Mem`: EncCost's `cwUpd`, the label kept
(Template's `liftRead`). -/
noncomputable def trialUpd (t : TrialPt) : Mem → Option X → Mem :=
  liftUpd (cwUpd t.l t.e t.x t.xi)

/-- The read projectors of the flip costs (CostLift's `PRof`): off the selection reads of each
trial's `h`-read, `0` on the other read ports. -/
noncomputable def PRm (L : HonestTable) (c : HwRead X Z Mem) :
    Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ :=
  PRof Prod.snd trialUpd L c

/-- The flip cost of the read ports, relative to the projectors `PRm L`. -/
noncomputable def dRof (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  flipCost (BadR L progCap) (hwReadKraus c) (PRm L c) σ

/-- The flip cost of the program ports, relative to the projector `0`. -/
noncomputable def dPof (L : HonestTable) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  flipCost (BadR L progCap) (hwProgKraus c) 0 σ

/-- A cost summed along the run of the canonical game `gameR A L` in `runtimeR` (record ports:
`0`). -/
noncomputable def costTot (A : Adversary (X × Z))
    (dR : HwRead X Z Mem → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost dR dP)) (gameR A L) initR

/-- The total classical (flip) cost of the run of the game. -/
noncomputable def twR (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (dRof L) (dPof L) L

/-- The codeword flips of the selecting reads with the flip terms `ε, ε'` of the other reads,
summed along the run (`encW + epsW`). -/
noncomputable def encEpsTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (fun c σ ↦ encW Prod.snd trialUpd (BadR L progCap) L c σ +
    epsW Prod.snd trialUpd (BadR L progCap) L c σ) (fun _ _ ↦ 0) L

/-- The flip terms `ε, ε'` of the reads other than the selecting reads, summed along the run. -/
noncomputable def epsTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (epsW Prod.snd trialUpd (BadR L progCap) L) (fun _ _ ↦ 0) L

/-- The recorded mass of the reads (the read cell recorded or hardwired), summed along the run
(`massW`). -/
noncomputable def massTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (massW Prod.snd trialUpd L) (fun _ _ ↦ 0) L

/-- The state-weighted counts `tr(σ · msgCwCount · 1_SR)` of the selecting reads of all trials of
all keys, summed along the run (`cntW`). -/
noncomputable def cntTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (cntW Prod.snd trialUpd L) (fun _ _ ↦ 0) L

/-- The flip costs of the program ports, summed along the run. -/
noncomputable def progTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (fun _ _ ↦ 0) (dPof L) L

/-- **The trace-weighted classical-call count**: the weight of the inputs of the read and program
calls, summed along the run (a call reached with weight `w` counts `w`). -/
noncomputable def callTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ σ ↦ ENNReal.ofReal σ.trace.re) L

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

/-- The cap of the joint weighted count of the selecting reads: `2^22 (6q + progCap)`, the
cross-key potential (one per adversary call and per program call) over the codeword rate
`ρ_c ≥ 2^-21`, with a factor `2` for the interference of the recorded cells. -/
def encCap (q : ℕ) : ℕ := 2 ^ 22 * (6 * q + progCap)

/-- The codeword flips of the selecting reads at the joint cap: `2^-128 encCap = (6q + progCap)
2^-106`. -/
noncomputable def encTerm (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128)⁻¹ * (encCap q : ℝ≥0∞)

/-- The target of the recorded mass of the reads: `3 · 6q · 2^21 · 2^-128 = 18q · 2^-107`. A
trial's cells (its `k`, `k'` and `h` reads) are recorded only if the adversary queried the trial's
block, which carries the hidden 128-bit randomizer base `R0` plus the trial counter: each adversary
entry at a key's message prefix matches a given trial with probability `2^-128` (not `2^32 · 2^-128
= 2^-96`, which charges every trial up to the attempt cap), the trials of a key weigh at most
`1 / ρ_c ≤ 2^21` (survival), and the `6q` adversary entries are shared among the keys. -/
noncomputable def massCap (q : ℕ) : ℝ≥0∞ :=
  ((18 * q * 2 ^ 21 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹

/-- The flip terms of the `k`, `k'` reads: `2^-300` per unit of call weight, at most `clsCap`
units (CostRun's `callTot_le_clsCap`; capacity scale: a filled `k`, `k'` cell flips the event for
`(T+1)((T+1)T + 2T) G` of the `2^512` values, `T ≤ 2^68`, `G = 18`). -/
noncomputable def epsCap : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (2 ^ 300 : ℝ≥0∞)⁻¹

/-- **Placeholder** target of the flip terms of the verification's `h`-reads (the reads that are
not `ReadOk`, CostRun's residual `epsRestWt`), averaged over the good tables: `3 · verifyBlocks ·
2^-120`, awaiting the refined read cost (ReadCost). -/
noncomputable def verifCap : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * (2 ^ 120 : ℝ≥0∞)⁻¹

/-- The programs: `2^-128` per program call averaged over the programmed honest value
(`flipCost_programH_avg_le`; `0` for intermediate `h` cells, capacity scale for `k`, `k'`). -/
noncomputable def progTerm : ℝ≥0∞ :=
  (progCap : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹

/-- **The classical costs**: `(√(encTerm + epsCap + verifCap) + √massCap)² + progTerm`, about
`2^-63.7` at `q = 2^30`, `2^-51.1` at `q = 2^50` and `2^-37.1` at `q = 2^64`. -/
noncomputable def clsBound (q : ℕ) : ℝ≥0∞ :=
  ((encTerm q + epsCap + verifCap) ^ (2⁻¹ : ℝ) + massCap q ^ (2⁻¹ : ℝ)) ^ 2 + progTerm

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
permutation calls and at most `lifetime` signing requests (needed for `q ≤ 2^64` only: above,
`qrpmBound q ≥ 1`). Data: the hidden sets `H` (honest values and the seed-keyed cells) and the
residual read flip terms `verifEps`. The event-bound program is the canonical game `gameR A`; the
classical costs (`encJoint`, `restMass`, `readEps`, `verifEpsBound`, `callsW`, `progRest`) are
along it. Runtime 1's table is FullTable's `fullHw` (`tableLe_fullHw`, `winProb_eq_uavg_full`);
the call counts are theorems from the budgets (`advCalls_gameR`, `clsCalls_gameR`,
`progCalls_gameR`, GameTCalls). -/
structure XmssQrpmDebts (q : ℕ) (A : Adversary (X × Z)) where
  Hh : HonestTable → Set Z
  Hk : HonestTable → Set X
  Hk' : HonestTable → Set X
  /-- The flip terms of the game's reads that are not `ReadOk` (the verification's `h`-reads),
  summed along the run: CostRun's `totalWeight (epsRestWt L) (gameR A L) initR`. -/
  verifEps : HonestTable → ℝ≥0∞
  /-- **Template/Reparam**: the hidden sets cover runtime 1's table (the seed-keyed cells inside). -/
  covers : ∀ L, Covers (fullHw L) (Hh L) (Hk L) (Hk' L)
  /-- **The graded hybrid, sponge ports** (Disclose with `viewByOn_gameT`, Seed, CoinStage,
  CoinPath): the hidden mass at the sponge ports, summed over the calls, averaged over the table. -/
  hybSponge : uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments
    (spongeMass (Hh L) (Hk L) (Hk' L)) (gameR A L) initR) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS
  /-- **The graded hybrid, read ports** (Disclose at the read ports): the hidden mass at the read
  ports, summed over the calls, averaged over the table. -/
  hybRead : uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments
    (readMass (Hh L) (Hk L) (Hk' L)) (gameR A L) initR) ≤ (clsCap : ℝ≥0∞) * kappaR
  /-- **End** (EndReads' `endReads_of_winDecomp` with `x := gameR A L`): on runs whose final
  hardwired cells are at most `progCap`, the verification's reads (the final reads) and the
  classification `win_imp_bad` bound the win of the game by the event `BadR L progCap` at the end
  of the game plus the read error. -/
  endReads : ∀ L, GradeCap m0R (gameR A L) → p2R (gameR A) L ≤ ewR (gameR A) L + readTerm
  /-- **The cross-key potential** (open): on good tables, the state-weighted counts of the
  selecting reads of all trials of all keys, summed along the game, are at most `encCap q`. Its
  proof is the potential `∑_{k unselected} msgCwCount(·, k)` (at most the message-slot cells,
  `sum_msgCwCount_le`): it grows by at most one per adversary call and per program call, and a
  trial read of key `k` removes `msgCwCount(·, k)` with probability `ρ_c` on its selection reads
  (`survive_getSelectRead_le`). -/
  encJoint : ∀ L, PermGood L.perm 18 → cntTot A L ≤ encCap q
  /-- **The recorded mass** (open; with the current read projectors the verification's reads of
  recorded cells count): the weight off the selection reads at the reads (the read cell recorded or
  hardwired), summed along the run, averaged over the good tables (`massCap`: the hidden randomizer
  base, survival, the adversary's entries). -/
  restMass : uavg (fun L ↦ if PermGood L.perm 18 then massTot A L else 0) ≤ massCap q
  /-- **The flip terms of the other reads** (CostRun's `epsTot_le_add`): capacity scale per unit
  of call weight, plus the residual `verifEps`. -/
  readEps : ∀ L, PermGood L.perm 18 → epsTot A L ≤ (2 ^ 300 : ℝ≥0∞)⁻¹ * callTot A L + verifEps L
  /-- **The verification's read flip terms** (open, awaiting the refined read cost, ReadCost):
  averaged over the good tables, at most the placeholder `verifCap`. -/
  verifEpsBound : uavg (fun L ↦ if PermGood L.perm 18 then verifEps L else 0) ≤ verifCap
  /-- **The trace-weighted classical calls of the game** (CostRun's `callTot_le_clsCap`). -/
  callsW : ∀ L, callTot A L ≤ clsCap
  /-- **The programs** (open: the view of the programmed honest value, and reprogrammed cells):
  `2^-128` per program call, at most `progCap` calls, averaged over the good tables. -/
  progRest : uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤ progTerm

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
theorem labelFree_badR (L : HonestTable) (N : ℕ) : LabelFree X Z HPos Selections (BadR L N) :=
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
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The canonical game's sponge calls**: at most `6q` (GameTCalls' `hN_sponge`). -/
theorem advCalls_gameR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (gameR A L)
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1)
      (6 * q) :=
  hN_sponge cwUpd A hperm hsign (pubOf L) (valueAt L)

/-- **The canonical game's classical calls** (reads, programs, records): at most `clsCap`
(GameTCalls' `hN_cls`). -/
theorem clsCalls_gameR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (gameR A L)
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0)
      clsCap :=
  hN_cls cwUpd A hperm hsign (pubOf L) (valueAt L)

/-- **The canonical game's program calls**: at most `progCap` (GameTCalls' `hN_prog`). -/
theorem progCalls_gameR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (gameR A L) (progChargeR HPos Selections) progCap :=
  hN_prog cwUpd A hperm hsign (pubOf L) (valueAt L)

/-- **The graded hybrid with record ports**, averaged over the table. -/
theorem uavg_p1R_le (d : XmssQrpmDebts q A) :
    uavg (p1R A fullHw) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := by
  refine (uavg_win_runtime1R_le_graded_total .instruments fullHw d.Hh d.Hk d.Hk' d.covers m0R
    (gameR A) (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs) (measurableSet_singleton true) (6 * q)
    (advCalls_gameR hperm hsign) _ _ d.hybSponge d.hybRead).trans_eq ?_
  rw [hybTerm, add_assoc]
  rfl

omit hperm hsign in
/-- S4's fresh bound for the slices of `BadR` (those of `Bad`, the label ignored). -/
theorem freshBound_slice_badR (L : HonestTable) (hπ : PermGood L.perm 18) (T : ℕ) (W : Hw X Z)
    (m : Mem) :
    FreshBound (slice (BadR L progCap) W m) T
      (preimageRateBound (X := X) (Z := Z) (progCap + T) 18 (2 ^ 960)) := by
  have : DecidablePred (· ∈ Bad L progCap) := fun _ ↦ Classical.propDecidable _
  convert freshBound_slice_bad (N := progCap) hπ T W m.2 using 1
  · ext D
    exact Iff.rfl

/-- **The prefix's sponge calls**: at most the game's (`advCalls_gameR`). -/
theorem advCalls_prefixR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (prefixR A L)
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1)
      (6 * q) := by
  have h := advCalls_gameR hperm hsign L
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

/-- **The prefix's classical calls**: at most the game's (`clsCalls_gameR`). -/
theorem clsCalls_prefixR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (prefixR A L)
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0)
      clsCap := by
  have h := clsCalls_gameR hperm hsign L
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

/-- **The event bound** at the end of the game, at a good table. -/
theorem ewR_le (L : HonestTable) (hπ : PermGood L.perm 18) :
    ewR (gameR A) L ≤ (advTerm q + twR A L ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := 6 * q) (K := clsCap) (BadR L progCap) (labelFree_badR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (empty_not_mem_bad m0) advEps
    (fun n _ ↦ advEps_ne_top n)
    (fun n _ W m ↦ freshBound_slice_badR L hπ (n + clsCap + 1) W m)
    (dRof L) (dPof L)
    (fun c σ hσ ↦ potential_hwReadKraus_le (BadR L progCap) (PRm L)
      (fun c ↦ (PRof_proj Prod.snd trialUpd L c).1) (fun c ↦ (PRof_proj Prod.snd trialUpd L c).2)
      c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR L progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (gameR A L) (advCalls_gameR hperm hsign L) (clsCalls_gameR hperm hsign L)
    (SubState.basis ())

omit hperm hsign in
open scoped ComplexOrder in
theorem initR_posSemidef : initR.PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).posSemidef

omit hperm hsign in
/-- **The classical costs** at a table: `(√encEpsTot + √massTot)² + progTot` (CostLift's per-port
split `flipCost_le_ports`, linear along the run, optimized over the split). -/
theorem twR_le (A : Adversary (X × Z)) (L : HonestTable) :
    twR A L ≤ (encEpsTot A L ^ (2⁻¹ : ℝ) + massTot A L ^ (2⁻¹ : ℝ)) ^ 2 + progTot A L :=
  le_sq_add_of_forall_lin fun _ hs ↦ totalWeight_le_lin (runtimeR m0R) .instruments _ _ _ _ _ _
    (extWeight_hwCost_le_lin _ _ _ (fun _ _ ↦ 0) _ _ _ fun c _ hσ ↦ (flipCost_le_ports Prod.snd
      trialUpd (fun m s ↦ (m.1, s)) (fun _ _ ↦ rfl) (BadR L progCap) (N := progCap)
      (fun _ ↦ Iff.rfl) (fun t m v ↦ liftUpd_cases (sel := fun s ↦ cwSel s t.l t.e t.x t.xi v)
        (cwUpd_some t.l t.e t.x t.xi m.2 v)) c hs hσ).trans_eq (add_zero _).symm)
    (gameR A L) initR_posSemidef

omit hperm hsign in
/-- **The codeword flips and the other reads' flip terms** at a good table: at most
`encTerm q + (epsCap + verifEps L)` (`encW_le_cntW`, `encJoint`, `readEps`, `callsW`). -/
theorem encEpsTot_le (d : XmssQrpmDebts q A) (L : HonestTable) (hπ : PermGood L.perm 18) :
    encEpsTot A L ≤ encTerm q + (epsCap + d.verifEps L) := by
  refine (totalWeight_le_add (runtimeR m0R) .instruments _ _ _ _ 1
    (extWeight_hwCost_le_add _ _ _ _ _ fun c _ hσ ↦ add_le_add
      (encW_le_cntW Prod.snd trialUpd (BadR L progCap) L c hσ) (one_mul _).ge)
    (gameR A L) initR_posSemidef).trans ?_
  rw [one_mul]
  refine add_le_add ?_ ((d.readEps L hπ).trans (add_le_add ?_ le_rfl))
  · unfold encTerm
    gcongr
    exact d.encJoint L hπ
  · unfold epsCap
    rw [mul_comm]
    gcongr
    exact d.callsW L

/-- **Runtime 2's win probability**, averaged over the table. -/
theorem uavg_p2R_le (d : XmssQrpmDebts q A) : uavg (p2R (gameR A)) ≤ eventTerm q := by
  set twg : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then twR A L else 0
  set bad : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then 0 else 1
  have hpt : ∀ L, p2R (gameR A) L ≤ (advTerm q + twg L ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + bad L := by
    intro L
    by_cases hπ : PermGood L.perm 18
    · have hg := gradeCap_of m0R (progCalls_gameR hperm hsign L) le_rfl
      have h := (d.endReads L hg).trans (add_le_add (ewR_le hperm hsign L hπ) le_rfl)
      simp only [twg, bad, hπ, ↓reduceIte, add_zero]
      exact h
    · simp only [bad, hπ, ↓reduceIte]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have htw : uavg twg ≤ clsBound q := by
    set vg : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then d.verifEps L else 0
    set mg : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then massTot A L else 0
    set pg : HonestTable → ℝ≥0∞ := fun L ↦ if PermGood L.perm 18 then progTot A L else 0
    have hpt : ∀ L, twg L ≤
        ((encTerm q + epsCap + vg L) ^ (2⁻¹ : ℝ) + mg L ^ (2⁻¹ : ℝ)) ^ 2 + pg L := fun L ↦ by
      by_cases hπ : PermGood L.perm 18
      · simp only [twg, vg, mg, pg, hπ, ↓reduceIte]
        refine (twR_le A L).trans (add_le_add (pow_le_pow_left₀ zero_le
          (add_le_add (ENNReal.rpow_le_rpow ((encEpsTot_le d L hπ).trans_eq (add_assoc _ _ _).symm)
            (by norm_num)) le_rfl) 2) le_rfl)
      · simp only [twg, hπ, ↓reduceIte]
        exact zero_le
    calc uavg twg
        ≤ uavg (fun L ↦ ((encTerm q + epsCap + vg L) ^ (2⁻¹ : ℝ) + mg L ^ (2⁻¹ : ℝ)) ^ 2 + pg L) :=
          uavg_mono hpt
      _ = uavg (fun L ↦ ((encTerm q + epsCap + vg L) ^ (2⁻¹ : ℝ) + mg L ^ (2⁻¹ : ℝ)) ^ 2) +
            uavg pg :=
          uavg_add _ _
      _ ≤ (uavg (fun L ↦ encTerm q + epsCap + vg L) ^ (2⁻¹ : ℝ) + uavg mg ^ (2⁻¹ : ℝ)) ^ 2 +
            progTerm :=
        add_le_add (uavg_sqrt_add_sqrt_sq_le (fun L ↦ encTerm q + epsCap + vg L) mg) d.progRest
      _ ≤ clsBound q := by
        rw [uavg_add, uavg_const]
        unfold clsBound
        exact add_le_add (pow_le_pow_left₀ zero_le (add_le_add
          (ENNReal.rpow_le_rpow (add_le_add le_rfl d.verifEpsBound) (by norm_num))
          (ENNReal.rpow_le_rpow d.restMass (by norm_num))) 2) le_rfl
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
  have hK : uavg (p1T A fullHw) = uavg (p1R A fullHw) :=
    congrArg uavg (funext fun L ↦ (p1T_eq_p1K A tableLe_fullHw L).trans (p1K_eq_p1R A fullHw L))
  calc winProb keccakStateEquiv A = uavg (p1T A fullHw) := winProb_eq_uavg_full A
    _ = uavg (p1R A fullHw) := hK
    _ ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := uavg_p1R_le hperm hsign d
    _ ≤ (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 := by
      gcongr
      exact uavg_p2R_le hperm hsign d

omit hperm hsign in
/-- The win probability is at most `1`. -/
theorem winProb_le_one (A : Adversary (X × Z)) : winProb keccakStateEquiv A ≤ 1 := by
  rw [winProb_eq_uavg_full A]
  refine (uavg_mono (g := fun _ ↦ (1 : ℝ≥0∞)) fun _ ↦ ?_).trans (uavg_const 1).le
  exact QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _

omit hperm hsign in
/-- **Above `2^64` permutation calls the bound is trivial**: the sponge-port hybrid term alone is
`√(4 · 6q · 6q κ) ≥ 12 q 2^-64 ≥ 1`. -/
theorem one_le_qrpmBound (hq : 2 ^ 64 < q) : 1 ≤ qrpmBound q := by
  have h6 : (2 : ℝ≥0∞) ^ 64 ≤ ((6 * q : ℕ) : ℝ≥0∞) := by
    have h : 2 ^ 64 ≤ 6 * q := hq.le.trans (by omega)
    exact_mod_cast h
  have hk : (2 ^ 128 : ℝ≥0∞)⁻¹ ≤ kappaS := by
    unfold kappaS
    exact le_self_add
  have h1 : (1 : ℝ≥0∞) ≤ ((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS) :=
    calc (1 : ℝ≥0∞) = 2 ^ 64 * (2 ^ 64 * (2 ^ 128)⁻¹) := by
          rw [← mul_assoc, ← pow_add, show 64 + 64 = 128 from rfl,
            ENNReal.mul_inv_cancel (by simp) (by simp)]
      _ ≤ _ := by gcongr
  have h2 : 1 ≤ hybTerm q := by
    unfold hybTerm
    refine le_trans ?_ le_self_add
    calc (1 : ℝ≥0∞) = 1 ^ (2⁻¹ : ℝ) := (ENNReal.one_rpow _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow (h1.trans (le_mul_of_one_le_left zero_le (by norm_num)))
          (by norm_num)
  unfold qrpmBound
  exact one_le_pow₀ (h2.trans le_add_self)

omit hperm hsign in
/-- **leanXMSS is quantum SUF-CMA secure in the QRPM** with bound `qrpmBound`, given the open
debts of every adversary within the budgets making at most `2^64` permutation calls (above, the
bound is at least `1`). Conditional: the unconditional theorem constructs the debts. -/
theorem leanXmss_qrpm_security_of_debts
    (hd : ∀ q (A : Adversary (X × Z)),
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q) →
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) →
      q ≤ 2 ^ 64 → XmssQrpmDebts q A) :
    QuantumStronglyUnforgeable keccakStateEquiv qrpmBound := fun q A hq hs ↦
  if hle : q ≤ 2 ^ 64 then winProb_le_qrpmBound hq hs (hd q A hq hs hle)
  else (winProb_le_one A).trans (one_le_qrpmBound (not_le.mp hle))

end proof

/-! ## The Disclose part of the hybrid sum -/

section disclose

/-- **The 128-bit hidden `k`-cells of the canonical game, per call** (Disclose with
`viewByOn_gameT`, through `uavg_hiddenK_digest_runtimeR_le`). For a reparametrization
`e : HonestTable ≃ P × (HPos → Digest)` of the table into public data and the hidden values,
and hidden `k`-cells `HkV p v` each naming an undisclosed position whose value it carries,
the hidden mass of the `j`-th call of the realized template game against `runtimeR`, averaged over
the table, is at most `2^-128`. -/
theorem uavg_hiddenK_digest_le {P : Type} [Fintype P] (A : Adversary (X × Z))
    (e : HonestTable ≃ P × (HPos → Digest)) (pubP : P → Pub)
    (HkV : P → (HPos → Digest) → Set X) (src : P → X → HwReg X Z Mem → HPos)
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
