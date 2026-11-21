module

public import Quantum.Sphincs.Assembly.RecordDrop
public import Quantum.Sphincs.Assembly.Costs

@[expose] public section

/-!
# leanSPHINCS's canonical runtime-2 game, the first step of the chain, and the event constants

**The canonical runtime-2 game** at a digest policy `pol`, public data `p` and hidden values `v`
(contract C4): `gameR pol A p v = realizeT v (gameT Selections cwUpd pol p A)` (Template; each
counter trial's `h`-read records a codeword selection with Events' `cwUpd`), run against
`runtimeR m0R` (runtime 2 with record ports). It is its challenge prefix `prefixR pol A p v`
followed by the verification (`gameR_eq`). The hybrid side runs it at `msgPol` and a table `L`
(`pubOf L`, `valueAt L`); the event side at `strPol` and template data `(p, v)`.

**G0 to runtime 1** (step 1 of the chain):
* `winProb_eq_uavg_p1T`: the win probability is the table average of runtime 1 with the full table
  `fullHw L` hardwired running the grind-only read game (FullTable's `winProb_eq_uavg_full` with
  GameT's `fullReads_gameReadsT`);
* `p1T_eq_p1K`: **program ports** (GameT's `dropsTo_gameD` with `progsOf_fullHw`): Kraus's
  runtime 1 on `gameD` has the same law, for any hardwired table extending `fullHw L`;
* `p1K_eq_p1R`: **record ports** (RecordDrop's `dropRec_gameT`, leanXMSS's
  `evalDistMap_runtime1R_eq`): runtime 1 with record ports on the canonical game at `msgPol`;
* `winProb_eq_uavg_p1R`: together, `winProb A = uavg (p1R A fullHw)`.

**The constants of the event bound**: the classical-call cap `clsCap` (GameTCalls' `clsCalls`:
reads, program and record calls) and the fresh bound `advEps v n` of the `n`-th adversary call
(Events' `freshBound_slice_bad` at `progCap + n + clsCap + 1` entries, `PermGood π 18`), at most
`2^-128 + 2 capRate + 2^16 price S★(v)` (`advEps_le`).

**The call counts** from the adversary's budgets (GameTCalls' `hN_*`): `advCalls_gameR`,
`clsCalls_gameR`, `progCalls_gameR` and the prefix's.
-/

open MeasureTheory Matrix IPFunctor
open scoped ENNReal Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common Common.SufCma
open HashSig (Message)
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (uavg runtime1)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR runtime1R realizeT realizeT_bind₂ extCls
  isChargeBound_of_bind₂ evalDistMap_runtime1R_eq evalDistMap_runtime1_eq_spongeHardwiredReadRuntime
  hwLe_refl)

namespace Quantum.Sphincs.Assembly

/-! ## The register and the game -/

section game

/-- No selection recorded. -/
def m0 : Selections := fun _ ↦ none

/-- The initial memory: nothing revealed, nothing selected. -/
def m0R : Mem HPos := (∅, m0)

/-- The game's win bit. -/
def winObs (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) : Bool := p.2.2

/-- **The canonical runtime-2 game** at the digest policy `pol`, the public data `p` and the hidden
values `v`: the template game, its trials' `h`-reads updating the selections with `cwUpd`. -/
noncomputable def gameR (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT v (gameT Selections cwUpd pol p A)

/-- **The challenge prefix of the canonical game**, the event-bound program. -/
noncomputable def prefixR (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SignLog Message (Option Signature))) :=
  realizeT v (prefixT Selections cwUpd pol p A)

/-- **The canonical game is its challenge prefix, then the verification.** -/
theorem gameR_eq (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    gameR pol A p v = (prefixR pol A p v).bind fun x ↦ realizeT v (verifyT Selections p x) :=
  (congrArg (realizeT v) (gameT_eq_prefixT_bind Selections cwUpd pol p A)).trans
    (realizeT_bind₂ _ _ _)

/-- The initial state of the runtimes with record ports, beside the adversary's trivial
register. -/
noncomputable def initR : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
    (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix

open scoped ComplexOrder in
theorem initR_posSemidef : initR.PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).posSemidef

end game

/-! ## G0 to runtime 1 with program and record ports -/

section chain

variable (A : SAdversary)

/-- Runtime 1 with the cells `Lt L` hardwired, running the grind-only read game at `L`. -/
noncomputable def p1T (Lt : HonestTable → Hw X Z) (L : HonestTable) : ℝ≥0∞ :=
  (spongeHardwiredReadRuntime X Z (Lt L) ()).evalDistMap .instruments
    (gameReadsT (pubOf L) (valueAt L) A) (SubState.basis ()) winObs {true}

/-- Kraus's runtime 1 (`Lt L` hardwired, program ports) running the canonical game with its record
ports dropped. -/
noncomputable def p1K (Lt : HonestTable → Hw X Z) (L : HonestTable) : ℝ≥0∞ :=
  (runtime1 X Z (Lt L) ()).evalDistMap .instruments (gameD (pubOf L) (valueAt L) A)
    (SubState.basis ()) winObs {true}

/-- Runtime 1 with record ports running the canonical game at `msgPol` and `L`. -/
noncomputable def p1R (Lt : HonestTable → Hw X Z) (L : HonestTable) : ℝ≥0∞ :=
  (runtime1R X Z (Lt L) m0R).evalDistMap .instruments (gameR msgPol A (pubOf L) (valueAt L))
    (SubState.basis ()) winObs {true}

/-- **G0 is the table average of runtime 1 with the full table, on the grind-only game.** -/
theorem winProb_eq_uavg_p1T :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A = uavg (p1T A fullHw) :=
  (winProb_eq_uavg_full (fullReads_gameReadsT A)).trans (congrArg uavg (funext fun _ ↦ rfl))

/-- **The program ports drop** (`dropsTo_gameD`, `progsOf_fullHw`): Kraus's runtime 1 on `gameD`
is runtime 1 on the grind-only game, for every hardwired table extending the full table. -/
theorem p1T_eq_p1K {Lt : HonestTable → Hw X Z}
    (hLt : ∀ L, Quantum.Xmss.Assembly.HwLe (fullHw L) (Lt L))
    (L : HonestTable) : p1T A Lt L = p1K A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (Lt L) ()
      (dropsTo_gameD ((progsOf_fullHw L).mono (hLt L)) A) (SubState.basis ()) winObs)).symm

/-- **The record ports drop** (`dropRec_gameT`, `evalDistMap_runtime1R_eq`): runtime 1 with record
ports on the canonical game at `msgPol` is Kraus's runtime 1 on `gameD`. -/
theorem p1K_eq_p1R (Lt : HonestTable → Hw X Z) (L : HonestTable) : p1K A Lt L = p1R A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1R_eq (Lt L) m0R
      (dropRec_gameT cwUpd (valueAt L) (pubOf L) A) (SubState.basis ())
      winObs)).symm

/-- **G0 to runtime 1 with record ports**: the win probability is the table average of runtime 1
with the full table and record ports running the canonical game at `msgPol`. -/
theorem winProb_eq_uavg_p1R :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A = uavg (p1R A fullHw) :=
  (winProb_eq_uavg_p1T A).trans (congrArg uavg (funext fun L ↦
    (p1T_eq_p1K A (fun _ ↦ hwLe_refl _) L).trans (p1K_eq_p1R A fullHw L)))

end chain

/-! ## The constants of the event bound -/

/-- **The classical-call cap**: the reads, program and record calls of the game (GameTCalls'
`clsCalls`: one reveal for the root; per signing request `9 · 2^32` counter-trial reads, `2700`
program calls and `9` reveals; `3 · 903` verification reads). -/
def clsCap : ℕ :=
  clsCalls

theorem clsCap_eq : clsCap = 1 + (9 * 2 ^ 32 + 2709) * signatureLimit + 3 * 903 :=
  clsCalls_eq

/-- **The fresh bound of the `n`-th adversary call** at the hidden values `v`: Events' rate of the
slices of `Bad` (Struct and Enc, `2^960` values of an `h` cell per target; coverage,
`2^838 coverMass S★(v)`) below `progCap + n + clsCap + 1` entries, for `PermGood π 18`. -/
noncomputable def advEps (v : (s : HPos) → XD s) (n : ℕ) : ℝ≥0∞ :=
  preimageRateBound (X := X) (Z := Z) (progCap + (n + clsCap + 1)) 18 (2 ^ 960) +
    preimageRateBound (X := X) (Z := Z) (progCap + (n + clsCap + 1)) 18
      (2 ^ 838 * coverMass (coverOf v))

theorem advEps_ne_top (v : (s : HPos) → XD s) (n : ℕ) : advEps v n ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨preimageRateBound_ne_top _ _ _, preimageRateBound_ne_top _ _ _⟩

/-- **The fresh bound is `κ + 2^16 price S★(v)`** with `κ = 2^-128 + 2 capRate` (Events'
`freshRate_le`). -/
theorem advEps_le (v : (s : HPos) → XD s) (n : ℕ) :
    advEps v n ≤ (2 ^ 128)⁻¹ + 2 * capRate (progCap + (n + clsCap + 1)) 18 +
      ENNReal.ofReal ((2 ^ 16 * price (coverOf v) : ℚ) : ℝ) :=
  freshRate_le _ _ _

/-! ## The call counts -/

section calls

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The canonical game's sponge calls**: at most `6q` (`hN_sponge`). -/
theorem advCalls_gameR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR pol A p v)
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1)
      (6 * q) :=
  hN_sponge cwUpd pol A hperm hsign p v

/-- **The canonical game's classical calls** (reads, programs, records): at most `clsCap`
(`hN_cls`). -/
theorem clsCalls_gameR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR pol A p v)
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0)
      clsCap :=
  hN_cls cwUpd pol A hperm hsign p v

/-- **The canonical game's program calls**: at most `progCap` (`hN_prog`). -/
theorem progCalls_gameR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR pol A p v)
      (portCharge (Xmss.extProgCharge X Z (Mem HPos) (recSpec HPos Selections))) progCap :=
  hN_prog cwUpd pol A hperm hsign p v

/-- **The prefix's sponge calls**: at most the game's. -/
theorem advCalls_prefixR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v)
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1)
      (6 * q) := by
  have h := advCalls_gameR hperm hsign pol p v
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

/-- **The prefix's classical calls**: at most the game's. -/
theorem clsCalls_prefixR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v)
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0)
      clsCap := by
  have h := clsCalls_gameR hperm hsign pol p v
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

/-- **The prefix's program calls**: at most the game's. -/
theorem progCalls_prefixR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v)
      (portCharge (Xmss.extProgCharge X Z (Mem HPos) (recSpec HPos Selections))) progCap := by
  have h := progCalls_gameR hperm hsign pol p v
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

end calls

end Quantum.Sphincs.Assembly

end
