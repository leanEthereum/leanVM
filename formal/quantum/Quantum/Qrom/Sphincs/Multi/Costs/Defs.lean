module

public import Quantum.Qrom.Sphincs.Multi.GameTSel
public import Quantum.Qrom.Sphincs.Multi.GameTFactsPre
public import Quantum.Qrom.Sphincs.Costs.Defs

@[expose] public section

/-!
# The classical costs of the `n`-user leanSPHINCS runtime 2: definitions

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.Defs`, in the shape of
`Quantum.Qrom.Xmss.Multi.Costs.Defs`. The event bound of runtime 2 pays, beside the adversary's
fresh flips, the refined cost of every classical port of the challenge prefix
`prefixQSN (strPolN n) A θ` (`twPQSN`).

* **The register and the event**: runtime 2 at the memory `QMemSN n` (the template's label and
  every user's selections), from `m0SN`; the event `BadRQN pk hon S` is Events' `BadQN pk hon S`
  read through the label. At the hidden values `θ` the users' public keys are `pkQN θ`, their
  honest cells `honQN θ` and their static covers `starQN θ`.
* **The trial reads** (`trialReadSN z κ`, GameTSel): `trialKeySN` recovers the cell and the key
  `κ = (i, K)` from the read port (`trialUpdSN_inj`).
* **The per-read weights** (`trialWSN`): `encWtSN pk` (on the empty read cells of an unselected
  key, the codeword cells of the key's encoding slot owned by its user, `encCwCountN`) and
  `recUWtSN` (the recorded read cells of an unselected key). With the memo no trial read meets a
  selected key (`NoSelQS`), so the single-user re-grind weights have no analog.
* **Their sums along the prefix** (`encPreSN`, `recUPreSN`, `recUMaskSN`) and the total cost
  `twPQSN`.
* **The ports of the prefix** (`PortOkQSN`, `EncFreeSN`, `PreInvQSN`, `PrefixInvQSN`): sponge and
  record ports, trial reads of encoding slots at the read cell's owner, programs of exempt cells;
  no hardwired encoding cell, no selection of the read key, no decompressed `⊥`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf msgPos Disclosures)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT liftRead initU initU_posSemidef
  extWeight extCls NoBot)

attribute [local irreducible] sphincsRom

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## The register -/

/-- **The memory of the `n`-user runtime 2**: the template's label and every user's selections. -/
abbrev QMemSN (n : ℕ) : Type := Finset (TPosN n) × SelMemN n

/-- The register of the `n`-user runtime 2 as a quantum register. -/
abbrev RDSN (n : ℕ) : QReg :=
  QReg.of (RRegSN n (SelMemN n))

/-- The initial operator of runtime 2 beside the adversary's trivial register. -/
noncomputable def initQSN :
    Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ :=
  initU (X := PairOut) (Z := Qrom.HashDomain) (m0SN (n := n))

theorem initQSN_posSemidef : (initQSN (n := n)).PosSemidef :=
  initU_posSemidef (X := PairOut) (Z := Qrom.HashDomain) (m0SN (n := n))

theorem ofReal_trace_initQSN_le_one : ENNReal.ofReal (initQSN (n := n)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) (m0SN (n := n))).init).trace_re_le_one

/-! ## The event -/

/-- The targets of Events' `sphTgtQN` on the memory with the label. -/
def tgtRSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (S : Fin n → Disclosures) :
    Hw PairOut Qrom.HashDomain → QMemSN n → Qrom.HashDomain → Set PairOut :=
  fun W mm ↦ sphTgtQN pk hon S W mm.2

/-- **The event of the `n`-user runtime 2**: Events' `BadQN pk hon S` with the label ignored. -/
abbrev BadRQN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (S : Fin n → Disclosures) :
    Set (RRegSN n (SelMemN n)) :=
  CellTargetBad (tgtRSN pk hon S)

variable {pk : Fin n → PublicKey} {hon : Fin n → HonestCells} {S : Fin n → Disclosures}

theorem mem_badRQN_iff {s : RRegSN n (SelMemN n)} :
    s ∈ BadRQN pk hon S ↔ (s.1, s.2.1, s.2.2.2) ∈ BadQN pk hon S :=
  Iff.rfl

/-- `BadRQN` does not read the memory label. -/
theorem labelFree_badRQN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (S : Fin n → Disclosures) :
    Quantum.Xmss.Assembly.LabelFree PairOut Qrom.HashDomain (TPosN n) (SelMemN n)
      (BadRQN pk hon S) :=
  fun _ _ _ _ _ ↦ Iff.rfl

theorem upClosed_slice_badRQN (W : Hw PairOut Qrom.HashDomain) (m : QMemSN n) :
    UpClosed (slice (BadRQN pk hon S) W m) :=
  upClosed_slice_cellTargetBad W m

/-- The start of runtime 2 is outside the event. -/
theorem empty_not_mem_badRQN (m₀ : QMemSN n) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty PairOut Qrom.HashDomain, m₀) :
      RRegSN n (SelMemN n)) ∉ BadRQN pk hon S :=
  empty_not_mem_badQN (pk := pk) (hon := hon) (S := S) m₀.2

/-- **The fresh bound of every slice**: `epsQN S = 2^-128 + ⨆ i, price (S i)`. -/
theorem freshBound_slice_badRQN (W : Hw PairOut Qrom.HashDomain) (m : QMemSN n) (t : ℕ) :
    FreshBound (slice (BadRQN pk hon S) W m) t (epsQN S) :=
  freshBound_slice_badQN (pk := pk) (hon := hon) (S := S) W m.2 t

/-- The users' public keys at the hidden values `θ`. -/
def pkQN (θ : TValsN n) (i : Fin n) : PublicKey :=
  (tabOf (userOf θ i)).publicKey

/-- The users' honest cells at the hidden values `θ`. -/
def honQN (θ : TValsN n) (i : Fin n) : HonestCells :=
  QTable.honCell (seedsOf θ i) (tabOf (userOf θ i))

/-- The users' static covers at the hidden values `θ`: user `i`'s stream's `starCover`. -/
noncomputable def starQN (θ : TValsN n) (i : Fin n) : Disclosures :=
  starCover (streamOf (userOf θ i))

theorem pkQN_eq (θ : TValsN n) : pkQN θ = (tabOfN θ).pks :=
  rfl

theorem honQN_eq (θ : TValsN n) : honQN θ = honCellN (seedsOf θ) (tabOfN θ) :=
  rfl

/-! ## Trial reads -/

/-- **The read cell and key of a trial read port** (`trialReadSN z κ` names `κ`,
`trialUpdSN_inj`); `none` at the other read ports. -/
noncomputable def trialKeySN :
    HwRead PairOut Qrom.HashDomain (QMemSN n) → Option (Qrom.HashDomain × UKeyS n)
  | .readH z u => @dite _ (∃ κ, u = trialUpdSN z κ) (Classical.propDecidable _)
      (fun h ↦ some (z, h.choose)) fun _ ↦ none
  | _ => none

theorem trialKeySN_trialReadSN (z : Qrom.HashDomain) (κ : UKeyS n) :
    trialKeySN (trialReadSN z κ) = some (z, κ) := by
  have h : ∃ κ', trialUpdSN z κ = trialUpdSN z κ' := ⟨κ, rfl⟩
  show @dite _ (∃ κ', trialUpdSN z κ = trialUpdSN z κ') (Classical.propDecidable _)
    (fun h ↦ some (z, h.choose)) (fun _ ↦ none) = some (z, κ)
  rw [dite_eq_left h]
  exact congrArg (fun k ↦ some (z, k)) (trialUpdSN_inj h.choose_spec).symm

/-- **The per-read weight of a state weight `w`**: at the trial read of key `κ` at the cell `z`,
`∑ w z κ s · σ_ss`; `0` at the other read ports. -/
noncomputable def trialWSN (w : Qrom.HashDomain → UKeyS n → RRegSN n (SelMemN n) → ℝ)
    (c : HwRead PairOut Qrom.HashDomain (QMemSN n))
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  match trialKeySN c with
  | some k => ENNReal.ofReal (∑ q, w k.1 k.2 q.2 * (σ q q).re)
  | none => 0

theorem trialWSN_trialReadSN (w : Qrom.HashDomain → UKeyS n → RRegSN n (SelMemN n) → ℝ)
    (z : Qrom.HashDomain) (κ : UKeyS n)
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) :
    trialWSN w (trialReadSN z κ) σ = ENNReal.ofReal (∑ q, w z κ q.2 * (σ q q).re) := by
  unfold trialWSN
  rw [trialKeySN_trialReadSN z κ]

open scoped Classical in
/-- **The Enc weight**: the codeword cells of the key's encoding slot owned by its user, on the
empty read cells of an unselected key. -/
noncomputable def encWtSN (pk : Fin n → PublicKey) (z : Qrom.HashDomain) (κ : UKeyS n)
    (s : RRegSN n (SelMemN n)) : ℝ :=
  if s.1.1 z = none ∧ memAtS s κ = none then (encCwCountN pk (unionH s) κ.1 κ.2 : ℝ) else 0

open scoped Classical in
/-- **The recorded unselected weight**: the recorded read cells of an unselected key. -/
noncomputable def recUWtSN (z : Qrom.HashDomain) (κ : UKeyS n) (s : RRegSN n (SelMemN n)) : ℝ :=
  if s.1.1 z ≠ none ∧ memAtS s κ = none then 1 else 0

/-! ## Sums along the challenge prefix -/

/-- A read weight summed along the challenge prefix (program and record ports: `0`). -/
noncomputable def preTotSN (A : MuAdversaryS n) (θ : TValsN n)
    (dR : HwRead PairOut Qrom.HashDomain (QMemSN n) →
      Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (runtimeR (m0SN (n := n))).totalWeight .instruments (extWeight (hwCost dR fun _ _ ↦ 0))
    (prefixQSN (strPolN n) A θ) initQSN

/-- The Enc weights along the prefix, at the public keys `pkQN θ`. -/
noncomputable def encPreSN (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  preTotSN A θ (trialWSN (encWtSN (pkQN θ)))

/-- The recorded unselected weights along the prefix. -/
noncomputable def recUPreSN (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  preTotSN A θ (trialWSN recUWtSN)

open scoped Classical in
/-- The recorded unselected weights on the tables with distinct `PK.seed`s, `0` elsewhere (with
colliding `PK.seed`s one user's search records the trial cells of another's). -/
noncomputable def recUMaskSN (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then recUPreSN A θ else 0

theorem recUMaskSN_of_pDistinct (A : MuAdversaryS n) {θ : TValsN n} (h : PDistinct (tabOfN θ)) :
    recUMaskSN A θ = recUPreSN A θ := by
  classical
  unfold recUMaskSN
  exact ite_eq_left h

/-- **The classical costs of the challenge prefix**: the refined read cost (`readCostT`) and the
program flip cost for the event `BadRQN pk hon S`, along the run of `prefixQSN (strPolN n) A θ`. -/
noncomputable def twPQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (S : Fin n → Disclosures) (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  (runtimeR (m0SN (n := n))).totalWeight .instruments
    (extWeight (hwCost (fun c σ ↦ readCostT (BadRQN pk hon S) c σ)
      fun c σ ↦ flipCost (BadRQN pk hon S) (hwProgKraus c) 0 σ))
    (prefixQSN (strPolN n) A θ) initQSN

/-! ## The ports of the prefix -/

/-- **The ports the challenge prefix calls**: sponge and record ports; trial reads at an encoding
slot of the read cell's owner; programs of exempt cells. -/
def PortOkQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) :
    (RSpecSN n (SelMemN n)).Port → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr c)) => ∃ z i K, slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2) ∧
      ownerS pk z = some i ∧ c = trialReadSN z (i, K)
  | .inl (.inr c) => ∃ z a, c = .programH z a ∧ ExemptCellN pk hon z
  | .inr _ => True

/-- **No hardwired encoding cell** of any user. -/
def EncFreeSN (pk : Fin n → PublicKey) (s : RRegSN n (SelMemN n)) : Prop :=
  ∀ x, (s.2.1.1 x).isSome → ∀ (i : Fin n) (K : Key), slotOf (pk i) x ≠ some (.enc K.1 K.2.1 K.2.2)

/-- **The invariant at the prefix's calls**: the port is `PortOkQSN`, the input supported on
`EncFreeSN` registers holding no selection of a trial read's key (`selOkS`), with no
decompressed `⊥`. -/
def PreInvQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (i : (RSpecSN n (SelMemN n)).Port)
    (τ : Matrix ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) ℂ) : Prop :=
  PortOkQSN pk hon i ∧
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ m.2)
      {s | EncFreeSN pk s} τ ∧
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ m.2)
      {s | selOkS i s} τ ∧
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((RSpecSN n (SelMemN n)).In i)
        ((RSpecSN n (SelMemN n)).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain (QMemSN n)) τ)

/-- **The prefix's calls satisfy `PreInvQSN`** (the hypothesis of `twPQSN_le`). -/
def PrefixInvQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (A : MuAdversaryS n)
    (θ : TValsN n) : Prop :=
  ∃ Q : ∀ (i : (RSpecSN n (SelMemN n)).Port) (E : QReg),
      Matrix (((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) × E)
        (((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) × E) ℂ → Prop,
    (∀ i E σ, Q i E σ → PreInvQSN pk hon i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR (m0SN (n := n))).ForallQueries .instruments Q (prefixQSN (strPolN n) A θ)
        initQSN

end Quantum.Qrom.Sphincs.Multi

end
