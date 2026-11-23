module

public import Quantum.Qrom.Xmss.GameTFacts
public import Quantum.Xmss.Assembly.CostRefined

@[expose] public section

/-!
# The classical costs of runtime 2: definitions

The event bound of runtime 2 (`Quantum.Xmss.Assembly.eventWeight_runtimeR_le`) pays, beside the
adversary's fresh flips, the refined cost of every classical port of the challenge prefix
`prefixQ A θ` (`twPQ`). Here are the objects that cost is split into.

* **The register and the event**: runtime 2 with record ports at the memory `QMem` (the template's
  label and Events' selections), from `m0Q`; the event `BadRQ hon` is Events' `BadQ hon` read
  through the label (`CellTargetBad` with the targets of the selections, `mem_badRQ_iff`).
* **The trial reads** (`trialRead z l e`): the `h`-read of a message-digest cell `z` of key
  `(l, e)` updating the selections with `cwUpd`; `trialKey` recovers `(z, l, e)` from the port.
* **The per-read weights** (`trialW` of a state weight; `0` off the trial reads):
  - `encWt`: on the empty read cells of an unselected key, the codeword cells of the key's message
    slot (`msgCwCount`): the Enc flips;
  - `selWt`: the empty read cells of a selected key (one target digest: the re-grind flips);
  - `recUWt`: the recorded read cells of an unselected key;
  - `recSWt`: the recorded read cells of a selected key whose value hits the selected digest
    (`RecHitQ`).
* **Their sums along the prefix** (`encPre`, `selPre`, `recUPre`, `recSPre`) and the total cost
  `twPQ`.
* **The ports of the prefix** (`PortOkQ`, `MsgFree`, `PreInvQ`): sponge and record ports, trial
  reads of message slots, programs of exempt cells; no hardwired message cell; no decompressed `⊥`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT liftRead initU initU_posSemidef
  extWeight extCls NoBot)

attribute [local irreducible] xmssRom

/-! ## The register -/

/-- **The memory of runtime 2**: the template's label and Events' selections. -/
abbrev QMem : Type := Finset HPos × SelMem

/-- The initial memory: nothing revealed, nothing selected. -/
def m0Q : QMem := (∅, fun _ _ ↦ none)

/-- The initial operator of runtime 2 beside the adversary's trivial register. -/
noncomputable def initQ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ :=
  initU (X := HashOutput) (Z := HashDomain) m0Q

/-- The register of runtime 2 as a quantum register. -/
abbrev RD : QReg :=
  QReg.of (RReg SelMem)

theorem initQ_posSemidef : initQ.PosSemidef :=
  initU_posSemidef (X := HashOutput) (Z := HashDomain) m0Q

theorem ofReal_trace_initQ_le_one : ENNReal.ofReal initQ.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).init).trace_re_le_one

/-- The register of runtime 2 projected to Events' register (the label dropped). -/
def projQ (s : RReg SelMem) : RomReg HashDomain HashOutput SelMem :=
  (s.1, s.2.1, s.2.2.2)

theorem unionH_projQ (s : RReg SelMem) : unionH (projQ s) = unionH s :=
  rfl

/-! ## The event -/

/-- The targets of Events' `xmssTgtQ` on the memory with the label. -/
def tgtR (hon : HonestCells) : Hw HashOutput HashDomain → QMem → HashDomain → Set HashOutput :=
  fun W mm ↦ xmssTgtQ hon W mm.2

/-- **The event of runtime 2**: Events' `BadQ hon` with the memory label ignored. -/
abbrev BadRQ (hon : HonestCells) : Set (RReg SelMem) :=
  CellTargetBad (tgtR hon)

variable {hon : HonestCells}

theorem mem_badRQ_iff {s : RReg SelMem} : s ∈ BadRQ hon ↔ projQ s ∈ BadQ hon :=
  Iff.rfl

/-- `BadRQ` does not read the memory label. -/
theorem labelFree_badRQ (hon : HonestCells) :
    Quantum.Xmss.Assembly.LabelFree HashOutput HashDomain HPos SelMem (BadRQ hon) :=
  fun _ _ _ _ _ ↦ Iff.rfl

theorem upClosed_slice_badRQ (W : Hw HashOutput HashDomain) (m : QMem) :
    UpClosed (slice (BadRQ hon) W m) :=
  upClosed_slice_cellTargetBad W m

/-- The start of runtime 2 is outside the event. -/
theorem empty_not_mem_badRQ (m₀ : QMem) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain, m₀) :
      RReg SelMem) ∉ BadRQ hon :=
  empty_not_mem_badQ (hon := hon) m₀.2

/-- **The fresh bound of every slice**: `2^-128`. -/
theorem freshBound_slice_badRQ (W : Hw HashOutput HashDomain) (m : QMem) (t : ℕ) :
    FreshBound (slice (BadRQ hon) W m) t (2 ^ 128)⁻¹ := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  rw [← fiber_div_card_hashOutput]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_xmssTgtQ_le (hon := hon) W m.2 x) _

/-- The event of the canonical table `θ`: the honest cells of `tabOf θ` at `seedOf θ`. -/
def honQ (θ : HPos → Digest) : HonestCells :=
  QTable.honCell (seedOf θ) (tabOf θ)

/-! ## Trial reads -/

/-- **The trial read** of key `(l, e)` at its message-digest cell `z`: Events' `cwUpd`, the label
kept. -/
def trialRead (z : HashDomain) (l : Layer) (e : KeyIndex) : HwRead HashOutput HashDomain QMem :=
  liftRead (.readH z (cwUpd l e z))

/-- The read cell and key of a read port at a message slot. -/
def trialKey : HwRead HashOutput HashDomain QMem → Option (HashDomain × Layer × KeyIndex)
  | .readH z _ =>
    match slotOf z with
    | some (.msg l e) => some (z, l, e)
    | _ => none
  | _ => none

theorem trialKey_trialRead {z : HashDomain} {l : Layer} {e : KeyIndex}
    (hz : slotOf z = some (.msg l e)) : trialKey (trialRead z l e) = some (z, l, e) := by
  show (match slotOf z with
    | some (.msg l e) => some (z, l, e)
    | _ => none) = some (z, l, e)
  rw [hz]

/-- **The per-read weight of a state weight `w`**: at a read port of a message slot with cell `z`
and key `(l, e)`, `∑ w z l e s · σ_ss`; `0` at the other read ports. -/
noncomputable def trialW (w : HashDomain → Layer → KeyIndex → RReg SelMem → ℝ)
    (c : HwRead HashOutput HashDomain QMem)
    (σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) : ℝ≥0∞ :=
  match trialKey c with
  | some k => ENNReal.ofReal (∑ q, w k.1 k.2.1 k.2.2 q.2 * (σ q q).re)
  | none => 0

theorem trialW_trialRead (w : HashDomain → Layer → KeyIndex → RReg SelMem → ℝ)
    {z : HashDomain} {l : Layer} {e : KeyIndex} (hz : slotOf z = some (.msg l e))
    (σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) :
    trialW w (trialRead z l e) σ = ENNReal.ofReal (∑ q, w z l e q.2 * (σ q q).re) := by
  unfold trialW
  rw [trialKey_trialRead hz]

open scoped Classical in
/-- **The Enc weight**: the codeword cells at the message slot of an unselected key, on the empty
read cells. -/
noncomputable def encWt (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : ℝ :=
  if s.1.1 z = none ∧ s.2.2.2 l e = none then (msgCwCount (unionH s) l e : ℝ) else 0

open scoped Classical in
/-- **The re-grind weight**: the empty read cells of a selected key. -/
noncomputable def selWt (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : ℝ :=
  if s.1.1 z = none ∧ s.2.2.2 l e ≠ none then 1 else 0

open scoped Classical in
/-- **The recorded unselected weight**: the recorded read cells of an unselected key. -/
noncomputable def recUWt (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : ℝ :=
  if s.1.1 z ≠ none ∧ s.2.2.2 l e = none then 1 else 0

/-- **A recorded hit of the selected digest**: the read cell `z` recorded with a value truncating
to the selected digest of the key `(l, e)`, selected at another cell. -/
def RecHitQ (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : Prop :=
  ∃ y sel, s.1.1 z = some y ∧ s.2.2.2 l e = some sel ∧ sel.1 ≠ z ∧ truncateHash y = sel.2

open scoped Classical in
/-- **The recorded selected weight**: `RecHitQ`. -/
noncomputable def recSWt (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : ℝ :=
  if RecHitQ z l e s then 1 else 0

/-! ## Sums along the challenge prefix -/

/-- A read weight summed along the challenge prefix (program and record ports: `0`). -/
noncomputable def preTot (A : Adversary) (θ : HPos → Digest)
    (dR : HwRead HashOutput HashDomain QMem →
      Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (runtimeR m0Q).totalWeight .instruments (extWeight (hwCost dR fun _ _ ↦ 0)) (prefixQ A θ) initQ

/-- The Enc weights along the prefix. -/
noncomputable def encPre (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  preTot A θ (trialW encWt)

/-- The re-grind weights along the prefix. -/
noncomputable def selPre (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  preTot A θ (trialW selWt)

/-- The recorded unselected weights along the prefix. -/
noncomputable def recUPre (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  preTot A θ (trialW recUWt)

/-- The recorded selected hits along the prefix. -/
noncomputable def recSPre (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  preTot A θ (trialW recSWt)

/-- **The classical costs of the challenge prefix**: the refined read cost (`readCostT`) and the
program flip cost for the event `BadRQ hon`, along the run of `prefixQ A θ` (record ports free). -/
noncomputable def twPQ (hon : HonestCells) (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  (runtimeR m0Q).totalWeight .instruments
    (extWeight (hwCost (fun c σ ↦ readCostT (BadRQ hon) c σ)
      fun c σ ↦ flipCost (BadRQ hon) (hwProgKraus c) 0 σ)) (prefixQ A θ) initQ

/-! ## The ports of the prefix -/

/-- **The ports the challenge prefix calls**: sponge and record ports; trial reads at a message
slot; programs of cells without a target once hardwired (`ExemptCell`). -/
def PortOkQ (hon : HonestCells) : (recHwSpec HashOutput HashDomain HPos SelMem).Port → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr c)) => ∃ z l e, slotOf z = some (.msg l e) ∧ c = trialRead z l e
  | .inl (.inr c) => ∃ z a, c = .programH z a ∧ ExemptCell hon z
  | .inr _ => True

/-- **No hardwired message cell.** -/
def MsgFree (s : RReg SelMem) : Prop :=
  ∀ x, (s.2.1.1 x).isSome → ∀ l e, slotOf x ≠ some (.msg l e)

/-- **The invariant at the prefix's calls**: the port is `PortOkQ`, the input supported on
`MsgFree` registers, with no decompressed `⊥`. -/
def PreInvQ (hon : HonestCells) (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port)
    (τ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem)
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem) ℂ) : Prop :=
  PortOkQ hon i ∧
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem ↦
      m.2) {s | MsgFree s} τ ∧
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem ↦
      m.2) {s | NoBot s} (MatrixMap.conj ((1 : Matrix
        ((recHwSpec HashOutput HashDomain HPos SelMem).In i)
        ((recHwSpec HashOutput HashDomain HPos SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) τ)

/-- **The prefix's calls satisfy `PreInvQ`** (the hypothesis of `twPQ_le`). -/
def PrefixInvQ (hon : HonestCells) (A : Adversary) (θ : HPos → Digest) : Prop :=
  ∃ P : ∀ (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port) (E : QReg),
      Matrix (((recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem) × E)
        (((recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem) × E) ℂ → Prop,
    (∀ i E σ, P i E σ → PreInvQ hon i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m0Q).ForallQueries .instruments P (prefixQ A θ) initQ

end Quantum.Qrom.Xmss

end
