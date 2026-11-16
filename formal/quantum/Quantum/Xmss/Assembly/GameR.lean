module

public import Quantum.Xmss.Assembly.ReparamR0
public import Quantum.Xmss.Assembly.CoversFull
public import Quantum.Xmss.Assembly.WinDecomp
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
# The canonical runtime-2 game, its costs and its call counts

The definitions of Security's chain that the cost and event modules (CostRun, ProgView, ProgSafe,
EventSqrt) build on, so that Security can import them. The canonical game's register has the
memory `Mem = Finset HPos × Selections`: the template's memory label and Events' selections. The
canonical runtime-2 game is `gameR A L = realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)`
(Template; each randomizer trial's `h`-read records a codeword selection with EncCost's `cwUpd`),
run against `runtimeR m0R` (runtime 2 with record ports). It is its challenge prefix
`prefixR A L = realizeT (valueAt L) (prefixT Selections cwUpd (pubOf L) A)` followed by the
verification (`gameR_eq`, Template's `gameT_eq_prefixT_bind`).

* **The event and the costs**: Events' `Bad` on the register with the memory label (`BadR`), its
  end weight `ewR`, CostLift's flip costs `dRof`, `dPof` and the totals along the run of the game
  (`costTot`, `twR`, `encEpsTot`, `epsTot`, `massTot`, `cntTot`, `progTot`, `callTot`).
* **The constants** of the event bound: the classical-call cap `clsCap`, the fresh bounds `advEps`
  and `advTerm`, the `k`, `k'` read flip terms `epsCap` and the programs' `progTerm`.
* **The call counts** from the adversary's budgets (GameTCalls): `advCalls_gameR`,
  `clsCalls_gameR`, `progCalls_gameR`, and the prefix's (`isChargeBound_of_bind₂`):
  `advCalls_prefixR`, `clsCalls_prefixR`.
-/

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Averages -/

section avg

variable {Θ : Type*} [Fintype Θ]

theorem uavg_const [Nonempty Θ] (c : ℝ≥0∞) : uavg (fun _ : Θ ↦ c) = c := by
  simp only [uavg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul]

theorem pow_two_rpow_inv_two (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end avg

/-! ## The register and the game -/

section game

/-- The memory of the runtimes: the template's label and Events' selections (its decidable
equality is WinDecomp's `winMemDecEq`). -/
abbrev Mem : Type := Finset HPos × Selections

/-- No selection recorded. -/
def m0 : Selections := fun _ _ ↦ none

/-- The initial memory: nothing disclosed, nothing selected. -/
def m0R : Mem := (∅, m0)

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

open scoped ComplexOrder in
theorem initR_posSemidef : initR.PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).posSemidef

end game

/-! ## The event and the costs along the game -/

section quantities

/-- **Events' `Bad` on the register with the memory label**: the label is ignored. -/
def BadR (L : HonestTable) (N : ℕ) : Set (HwReg X Z Mem) :=
  {r | (r.1, r.2.1, r.2.2.2) ∈ Bad L N}

/-- Membership in `BadR`, decided classically. -/
noncomputable local instance badRDec (L : HonestTable) (N : ℕ) : DecidablePred (· ∈ BadR L N) :=
  fun _ ↦ Classical.propDecidable _

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

/-- The program charge of runtime 2 with record ports. -/
abbrev progChargeR (S M' : Type) [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] :=
  portCharge (L := LocalSig.instruments.{0})
    (extProgCharge X Z (Finset S × M') (recSpec S M'))

/-! ## The constants of the event bound -/

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

/-- The flip terms of the `k`, `k'` reads: `2^-300` per unit of call weight, at most `clsCap`
units (CostRun's `callTot_le_clsCap`; capacity scale: a filled `k`, `k'` cell flips the event for
`(T+1)((T+1)T + 2T) G` of the `2^512` values, `T ≤ 2^68`, `G = 18`). -/
noncomputable def epsCap : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (2 ^ 300 : ℝ≥0∞)⁻¹

/-- The programs: `2^-128` per program call averaged over the programmed honest value
(`flipCost_programH_avg_le`; `0` for intermediate `h` cells, capacity scale for `k`, `k'`). -/
noncomputable def progTerm : ℝ≥0∞ :=
  (progCap : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹

/-! ## The event's slices and the call counts -/

section calls

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

/-- S4's fresh bound for the slices of `BadR` (those of `Bad`, the label ignored). -/
theorem freshBound_slice_badR (L : HonestTable) (hπ : PermGood L.perm 18) (T : ℕ) (W : Hw X Z)
    (m : Mem) :
    FreshBound (slice (BadR L progCap) W m) T
      (preimageRateBound (X := X) (Z := Z) (progCap + T) 18 (2 ^ 960)) := by
  have : DecidablePred (· ∈ Bad L progCap) := fun _ ↦ Classical.propDecidable _
  convert freshBound_slice_bad (N := progCap) hπ T W m.2 using 1
  · ext D
    exact Iff.rfl

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

end calls

end Quantum.Xmss.Assembly

end
