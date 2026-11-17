module

public import Quantum.Qrom.Xmss.Multi.GameTSel
public import Quantum.Qrom.Xmss.Multi.GameTFacts
public import Quantum.Qrom.Xmss.Costs.Bound

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: definitions

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.Defs`. The event bound of runtime 2 pays, beside
the adversary's fresh flips, the refined cost of every classical port of the challenge prefix
`prefixQN A θ` (`twPQN`).

* **The register and the event**: runtime 2 at the memory `QMemN n` (the template's label and
  every user's selections), from `m0N`; the event `BadRQN hon P` is Events' `BadQN hon P` read
  through the label.
* **The trial reads** (`trialReadN z κ`, GameTSel): `trialKeyN P` recovers the cell and the key
  `(i, l, e)` from the read cell (its message slot and its owner under `P`).
* **The per-read weights** (`trialWN P`): `encWtN P` (on the empty read cells of an unselected key,
  the codeword cells of its owner's key, `msgCwCountN`) and `recUWtN` (the recorded read cells of
  an unselected key). With the memo no trial read meets a selected key (`NoSelQ`), so the
  single-user re-grind weights have no analog.
* **Their sums along the prefix** (`encPreN`, `recUPreN`) and the total cost `twPQN`.
* **The ports of the prefix** (`PortOkQN`, `MsgFreeN`, `PreInvQN`, `PrefixInvQN`): sponge and
  record ports, trial reads of message slots at their owner, programs of exempt cells off the
  message slots; no hardwired message cell, no selection of the read key, no decompressed `⊥`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT liftRead initU initU_posSemidef
  extWeight extCls NoBot)
open Quantum.Qrom.MultiUser (ownerOf)

attribute [local irreducible] xmssRom

variable {n : ℕ}

/-! ## The register -/

/-- **The memory of the `n`-user runtime 2**: the template's label and every user's selections. -/
abbrev QMemN (n : ℕ) : Type := Finset (HPosN n) × SelMemN n

/-- The register of the `n`-user runtime 2 as a quantum register. -/
abbrev RDN (n : ℕ) : QReg :=
  QReg.of (RRegN n (SelMemN n))

/-- The initial operator of runtime 2 beside the adversary's trivial register. -/
noncomputable def initQN : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ :=
  initU (X := HashOutput) (Z := HashDomain) (m0N (n := n))

theorem initQN_posSemidef : (initQN (n := n)).PosSemidef :=
  initU_posSemidef (X := HashOutput) (Z := HashDomain) (m0N (n := n))

theorem ofReal_trace_initQN_le_one : ENNReal.ofReal (initQN (n := n)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).init).trace_re_le_one

/-! ## The event -/

/-- The targets of Events' `xmssTgtQN` on the memory with the label. -/
def tgtRN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    Hw HashOutput HashDomain → QMemN n → HashDomain → Set HashOutput :=
  fun W mm ↦ xmssTgtQN hon P W mm.2

/-- **The event of the `n`-user runtime 2**: Events' `BadQN hon P` with the label ignored. -/
abbrev BadRQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    Set (RRegN n (SelMemN n)) :=
  CellTargetBad (tgtRN hon P)

variable {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}

theorem mem_badRQN_iff {s : RRegN n (SelMemN n)} :
    s ∈ BadRQN hon P ↔ (s.1, s.2.1, s.2.2.2) ∈ BadQN hon P :=
  Iff.rfl

/-- `BadRQN` does not read the memory label. -/
theorem labelFree_badRQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    Quantum.Xmss.Assembly.LabelFree HashOutput HashDomain (HPosN n) (SelMemN n) (BadRQN hon P) :=
  fun _ _ _ _ _ ↦ Iff.rfl

theorem upClosed_slice_badRQN (W : Hw HashOutput HashDomain) (m : QMemN n) :
    UpClosed (slice (BadRQN hon P) W m) :=
  upClosed_slice_cellTargetBad W m

/-- The start of runtime 2 is outside the event. -/
theorem empty_not_mem_badRQN (m₀ : QMemN n) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain, m₀) :
      RRegN n (SelMemN n)) ∉ BadRQN hon P :=
  empty_not_mem_badQN (hon := hon) (P := P) m₀.2

/-- **The fresh bound of every slice**: `2^-128`. -/
theorem freshBound_slice_badRQN (W : Hw HashOutput HashDomain) (m : QMemN n) (t : ℕ) :
    FreshBound (slice (BadRQN hon P) W m) t (2 ^ 128)⁻¹ := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  rw [← fiber_div_card_hashOutput]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast card_xmssTgtQN_le (hon := hon) (P := P) W m.2 x) _

/-- The event of the hidden values `θ`: every user's honest cells. -/
def honQN (θ : HPosN n → Digest) : Fin n → HonestCells :=
  honN (seedsOf θ) (tabOfN θ)

/-- The users' public parameters at the hidden values `θ`. -/
def parQN (θ : HPosN n → Digest) : Fin n → PublicParameter :=
  (tabOfN θ).params

/-! ## Trial reads -/

/-- **The read cell and key of a trial read port** (`trialReadN z κ` names `κ`,
`trialUpdN_inj`); `none` at the other read ports. -/
noncomputable def trialKeyN :
    HwRead HashOutput HashDomain (QMemN n) → Option (HashDomain × UKey n)
  | .readH z u => @dite _ (∃ κ, u = trialUpdN z κ) (Classical.propDecidable _)
      (fun h ↦ some (z, h.choose)) fun _ ↦ none
  | _ => none

theorem trialKeyN_trialReadN (z : HashDomain) (κ : UKey n) :
    trialKeyN (trialReadN z κ) = some (z, κ) := by
  have h : ∃ κ', trialUpdN z κ = trialUpdN z κ' := ⟨κ, rfl⟩
  show @dite _ (∃ κ', trialUpdN z κ = trialUpdN z κ') (Classical.propDecidable _)
    (fun h ↦ some (z, h.choose)) (fun _ ↦ none) = some (z, κ)
  rw [dite_eq_left h]
  exact congrArg (fun k ↦ some (z, k)) (trialUpdN_inj h.choose_spec).symm

/-- **The per-read weight of a state weight `w`**: at the trial read of key `κ` at the cell `z`,
`∑ w z κ s · σ_ss`; `0` at the other read ports. -/
noncomputable def trialWN (w : HashDomain → UKey n → RRegN n (SelMemN n) → ℝ)
    (c : HwRead HashOutput HashDomain (QMemN n))
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  match trialKeyN c with
  | some k => ENNReal.ofReal (∑ q, w k.1 k.2 q.2 * (σ q q).re)
  | none => 0

theorem trialWN_trialReadN (w : HashDomain → UKey n → RRegN n (SelMemN n) → ℝ)
    (z : HashDomain) (κ : UKey n)
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) :
    trialWN w (trialReadN z κ) σ = ENNReal.ofReal (∑ q, w z κ q.2 * (σ q q).re) := by
  unfold trialWN
  rw [trialKeyN_trialReadN z κ]

open scoped Classical in
/-- **The Enc weight**: the codeword cells of the owner's key at the message slot, on the empty read
cells of an unselected key. -/
noncomputable def encWtN (P : Fin n → PublicParameter) (z : HashDomain) (κ : UKey n)
    (s : RRegN n (SelMemN n)) : ℝ :=
  if s.1.1 z = none ∧ memAt s κ = none then
    (msgCwCountN P (unionH s) κ.1 κ.2.1 κ.2.2 : ℝ) else 0

open scoped Classical in
/-- **The recorded unselected weight**: the recorded read cells of an unselected key. -/
noncomputable def recUWtN (z : HashDomain) (κ : UKey n) (s : RRegN n (SelMemN n)) : ℝ :=
  if s.1.1 z ≠ none ∧ memAt s κ = none then 1 else 0

/-! ## Sums along the challenge prefix -/

/-- A read weight summed along the challenge prefix (program and record ports: `0`). -/
noncomputable def preTotN (A : MuAdversary n) (θ : HPosN n → Digest)
    (dR : HwRead HashOutput HashDomain (QMemN n) →
      Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (runtimeR (m0N (n := n))).totalWeight .instruments (extWeight (hwCost dR fun _ _ ↦ 0))
    (prefixQN A θ) initQN

/-- The Enc weights along the prefix. -/
noncomputable def encPreN (P : Fin n → PublicParameter) (A : MuAdversary n)
    (θ : HPosN n → Digest) : ℝ≥0∞ :=
  preTotN A θ (trialWN (encWtN P))

/-- The recorded unselected weights along the prefix. -/
noncomputable def recUPreN (A : MuAdversary n) (θ : HPosN n → Digest) : ℝ≥0∞ :=
  preTotN A θ (trialWN recUWtN)

open scoped Classical in
/-- The recorded unselected weights on the tables with distinct public parameters, `0` elsewhere
(with colliding parameters one user's search records the trial cells of another's). -/
noncomputable def recUMaskN (A : MuAdversary n) (θ : HPosN n → Digest) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then recUPreN A θ else 0

theorem recUMaskN_of_pDistinct (A : MuAdversary n) {θ : HPosN n → Digest}
    (h : PDistinct (tabOfN θ)) : recUMaskN A θ = recUPreN A θ := by
  classical
  unfold recUMaskN
  exact ite_eq_left h

/-- **The classical costs of the challenge prefix**: the refined read cost (`readCostT`) and the
program flip cost for the event `BadRQN hon P`, along the run of `prefixQN A θ`. -/
noncomputable def twPQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (A : MuAdversary n) (θ : HPosN n → Digest) : ℝ≥0∞ :=
  (runtimeR (m0N (n := n))).totalWeight .instruments
    (extWeight (hwCost (fun c σ ↦ readCostT (BadRQN hon P) c σ)
      fun c σ ↦ flipCost (BadRQN hon P) (hwProgKraus c) 0 σ)) (prefixQN A θ) initQN

/-! ## The ports of the prefix -/

/-- **The ports the challenge prefix calls**: sponge and record ports; trial reads at a message
slot of the read cell's owner; programs of exempt cells off the message slots. -/
def PortOkQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    (RSpecN n (SelMemN n)).Port → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr c)) => ∃ z i l e, slotOf z = some (.msg l e) ∧
      ownerOf P prefixOf z = some i ∧ c = trialReadN z (i, l, e)
  | .inl (.inr c) => ∃ z a, c = .programH z a ∧ ExemptCellN hon P z ∧
      ∀ l e, slotOf z ≠ some (.msg l e)
  | .inr _ => True

/-- **No hardwired message cell.** -/
def MsgFreeN (s : RRegN n (SelMemN n)) : Prop :=
  ∀ x, (s.2.1.1 x).isSome → ∀ l e, slotOf x ≠ some (.msg l e)

/-- **The invariant at the prefix's calls**: the port is `PortOkQN`, the input supported on
`MsgFreeN` registers holding no selection of a trial read's key (`selOk`), with no decompressed
`⊥`. -/
def PreInvQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (i : (RSpecN n (SelMemN n)).Port)
    (τ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ) : Prop :=
  PortOkQN hon P i ∧
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
      {s | MsgFreeN s} τ ∧
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
      {s | selOk i s} τ ∧
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((RSpecN n (SelMemN n)).In i)
        ((RSpecN n (SelMemN n)).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain (QMemN n)) τ)

/-- **The prefix's calls satisfy `PreInvQN`** (the hypothesis of `twPQN_le`). -/
def PrefixInvQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) (A : MuAdversary n)
    (θ : HPosN n → Digest) : Prop :=
  ∃ Q : ∀ (i : (RSpecN n (SelMemN n)).Port) (E : QReg),
      Matrix (((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) × E)
        (((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) × E) ℂ → Prop,
    (∀ i E σ, Q i E σ → PreInvQN hon P i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR (m0N (n := n))).ForallQueries .instruments Q (prefixQN A θ) initQN

end Quantum.Qrom.Xmss.Multi

end
