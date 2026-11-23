module

public import Quantum.Qrom.Sphincs.GameT
public import Quantum.Xmss.Assembly.CostRefined

@[expose] public section

/-!
# The classical costs of leanSPHINCS's runtime 2: definitions

The event bound of runtime 2 (`Quantum.Xmss.Assembly.eventWeight_runtimeR_le`) pays, beside the
adversary's fresh flips, the refined cost of every classical port of the challenge prefix
`prefixQ pol A θ` (`twPQ`). Here are the objects that cost is split into (the leanSPHINCS
counterpart of `Quantum.Qrom.Xmss` `Costs/Defs`).

* **The register and the event**: runtime 2 with record ports at the memory `QMem` (the template's
  label and Events' selections), from `m0Q`; the event `BadRQ pk hon S` is Events' `BadQ pk hon S`
  read through the label (`CellTargetBad` of `sphTgtQ`, `mem_badRQ_iff`). At the hidden values
  `θ` the public key is `pkQ θ` and the honest cells `honQ θ`.
* **The trial reads** (`trialRead z K`): the read of an encoding cell `z` of key `K` updating the
  selections with `cwUpd`; `trialKey pk` recovers `(z, K)` from the port at an encoding slot.
* **The per-read weights** (`trialW pk` of a state weight; `0` off the trial reads):
  - `encWt pk`: on the empty read cells of an unselected key, the codeword cells of the key's
    encoding slot (`encCwCount`): the Enc flips;
  - `selWt`: the empty read cells of a selected key (one target digest: the re-grind flips);
  - `recUWt`: the recorded read cells of an unselected key;
  - `recSWt`: the recorded read cells of a selected key whose pair hits the selected digest
    (`RecHitQ`).
* **Their sums along the prefix** (`encPre`, `selPre`, `recUPre`, `recSPre`, at the public key
  `pkQ θ`) and the total cost `twPQ`.
* **The ports of the prefix** (`PortOkQ`, `EncFree`, `PreInvQ`): sponge and record ports, trial
  reads of encoding slots, programs of exempt cells; no hardwired encoding cell; no decompressed
  `⊥`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT liftRead initU initU_posSemidef
  extWeight extCls NoBot)

attribute [local irreducible] sphincsRom

/-! ## The register -/

/-- **The memory of runtime 2**: the template's label and Events' selections. -/
abbrev QMem : Type := Finset TPos × SelMem

/-- The initial memory: nothing revealed, nothing selected. -/
def m0Q : QMem := (∅, fun _ ↦ none)

/-- **The register of runtime 2** (GameTFacts' `RRegS SelMem`). -/
abbrev RegQ : Type := HwReg PairOut Qrom.HashDomain QMem

/-- The initial operator of runtime 2 beside the adversary's trivial register. -/
noncomputable def initQ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ :=
  initU (X := PairOut) (Z := Qrom.HashDomain) m0Q

/-- The register of runtime 2 as a quantum register. -/
abbrev RD : QReg :=
  QReg.of RegQ

theorem initQ_posSemidef : initQ.PosSemidef :=
  initU_posSemidef (X := PairOut) (Z := Qrom.HashDomain) m0Q

theorem ofReal_trace_initQ_le_one : ENNReal.ofReal initQ.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).init).trace_re_le_one

/-- The register of runtime 2 projected to Events' register (the label dropped). -/
def projQ (s : RegQ) : RomReg Qrom.HashDomain PairOut SelMem :=
  (s.1, s.2.1, s.2.2.2)

theorem unionH_projQ (s : RegQ) : unionH (projQ s) = unionH s :=
  rfl

/-! ## The event -/

/-- The targets of Events' `sphTgtQ` on the memory with the label. -/
def tgtR (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures) :
    Hw PairOut Qrom.HashDomain → QMem → Qrom.HashDomain → Set PairOut :=
  fun W mm ↦ sphTgtQ pk hon S W mm.2

/-- **The event of runtime 2**: Events' `BadQ pk hon S` with the memory label ignored. -/
abbrev BadRQ (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures) :
    Set RegQ :=
  CellTargetBad (tgtR pk hon S)

variable {pk : PublicKey} {hon : HonestCells} {S : Quantum.Sphincs.Disclosures}

theorem mem_badRQ_iff {s : RegQ} : s ∈ BadRQ pk hon S ↔ projQ s ∈ BadQ pk hon S :=
  Iff.rfl

/-- `BadRQ` does not read the memory label. -/
theorem labelFree_badRQ (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures) :
    Quantum.Xmss.Assembly.LabelFree PairOut Qrom.HashDomain TPos SelMem (BadRQ pk hon S) :=
  fun _ _ _ _ _ ↦ Iff.rfl

theorem upClosed_slice_badRQ (W : Hw PairOut Qrom.HashDomain) (m : QMem) :
    UpClosed (slice (BadRQ pk hon S) W m) :=
  upClosed_slice_cellTargetBad W m

/-- The start of runtime 2 is outside the event. -/
theorem empty_not_mem_badRQ (m₀ : QMem) :
    (((Database.empty, Database.empty, Database.empty), hwEmpty PairOut Qrom.HashDomain, m₀) :
      RegQ) ∉ BadRQ pk hon S :=
  empty_not_mem_badQ (pk := pk) (hon := hon) (S := S) m₀.2

/-- **The fresh bound of every slice**: `2^-128 + price S`. -/
theorem freshBound_slice_badRQ (W : Hw PairOut Qrom.HashDomain) (m : QMem) (t : ℕ) :
    FreshBound (slice (BadRQ pk hon S) W m) t
      ((2 ^ 128)⁻¹ + ENNReal.ofReal (Quantum.Sphincs.price S)) :=
  freshBound_slice_badQ (pk := pk) (hon := hon) (S := S) W m.2 t

/-- The public key of the canonical table `θ`. -/
def pkQ (θ : TVals) : PublicKey :=
  (tabOf θ).publicKey

/-- The honest cells of the canonical table `θ` at the master seed `seedOf θ`. -/
def honQ (θ : TVals) : HonestCells :=
  QTable.honCell (seedOf θ) (tabOf θ)

theorem pkQ_publicSeed (θ : TVals) : (pkQ θ).publicSeed = (tabOf θ).publicSeed :=
  rfl

/-! ## Trial reads -/

/-- **An encoding cell is at its key's encoding slot** under a public key with its `PK.seed`. -/
theorem slotOf_encCell (pk : PublicKey) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) (c : EncodingCounter) :
    slotOf pk (encCell pk.publicSeed l τ e m c) = some (.enc l τ e) := by
  rw [slotOf_of_encodeInput_eq_some _ (encodeInput_encCell pk.publicSeed l τ e m c)]
  exact slotOfInput_tweakable pk (.encoding l τ e) trivial _
    (by simp [littleEndianBytes, bigEndianBytes]) (by simp [littleEndianBytes, bigEndianBytes])

/-- A trial cell of a search is at its key's encoding slot. -/
theorem slotOf_trialCell (pk : PublicKey) (K : Key) (m : Digest) (c : ℕ) :
    slotOf pk (trialCell pk.publicSeed K m c) = some (.enc K.1 K.2.1 K.2.2) :=
  slotOf_encCell pk _ _ _ _ _

/-- **The memory update of a trial read** of key `K` at cell `z`, on the memory with the label. -/
def trialUpdQ (K : Key) (z : Qrom.HashDomain) : QMem → Option PairOut → QMem :=
  fun m o ↦ (m.1, cwUpd K z m.2 o)

/-- **The trial read** of key `K` at its encoding cell `z`: Events' `cwUpd`, the label kept. -/
def trialRead (z : Qrom.HashDomain) (K : Key) : HwRead PairOut Qrom.HashDomain QMem :=
  liftRead (.readH z (cwUpd K z))

theorem trialRead_eq (z : Qrom.HashDomain) (K : Key) :
    trialRead z K = .readH z (trialUpdQ K z) :=
  rfl

theorem cwUpd_of_ne_none {K : Key} {z : Qrom.HashDomain} {m : SelMem} (hm : m K ≠ none)
    (o : Option PairOut) : cwUpd K z m o = m := by
  cases o with
  | none => rfl
  | some v => exact ite_eq_right hm

/-- The read cell and key of a read port at an encoding slot for the public key `pk`. -/
def trialKey (pk : PublicKey) : HwRead PairOut Qrom.HashDomain QMem →
    Option (Qrom.HashDomain × Key)
  | .readH z _ =>
    match slotOf pk z with
    | some (.enc l τ e) => some (z, (l, τ, e))
    | _ => none
  | _ => none

theorem trialKey_trialRead {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) :
    trialKey pk (trialRead z K) = some (z, K) := by
  show (match slotOf pk z with
    | some (.enc l τ e) => some (z, (l, τ, e))
    | _ => none) = some (z, K)
  rw [hz]

/-- **The per-read weight of a state weight `w`**: at a read port of an encoding slot with cell `z`
and key `K`, `∑ w z K s · σ_ss`; `0` at the other read ports. -/
noncomputable def trialW (pk : PublicKey) (w : Qrom.HashDomain → Key → RegQ → ℝ)
    (c : HwRead PairOut Qrom.HashDomain QMem) (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) :
    ℝ≥0∞ :=
  match trialKey pk c with
  | some k => ENNReal.ofReal (∑ q, w k.1 k.2 q.2 * (σ q q).re)
  | none => 0

theorem trialW_trialRead (w : Qrom.HashDomain → Key → RegQ → ℝ) {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) :
    trialW pk w (trialRead z K) σ = ENNReal.ofReal (∑ q, w z K q.2 * (σ q q).re) := by
  unfold trialW
  rw [trialKey_trialRead hz]

open scoped Classical in
/-- **The Enc weight**: the codeword cells at the encoding slot of an unselected key, on the empty
read cells. -/
noncomputable def encWt (pk : PublicKey) (z : Qrom.HashDomain) (K : Key) (s : RegQ) : ℝ :=
  if s.1.1 z = none ∧ s.2.2.2 K = none then (encCwCount pk (unionH s) K : ℝ) else 0

open scoped Classical in
/-- **The re-grind weight**: the empty read cells of a selected key. -/
noncomputable def selWt (z : Qrom.HashDomain) (K : Key) (s : RegQ) : ℝ :=
  if s.1.1 z = none ∧ s.2.2.2 K ≠ none then 1 else 0

open scoped Classical in
/-- **The recorded unselected weight**: the recorded read cells of an unselected key. -/
noncomputable def recUWt (z : Qrom.HashDomain) (K : Key) (s : RegQ) : ℝ :=
  if s.1.1 z ≠ none ∧ s.2.2.2 K = none then 1 else 0

/-- **A recorded hit of the selected digest**: the read cell `z` recorded with a pair whose digest
is the selected digest of the key `K`, selected at another cell. -/
def RecHitQ (z : Qrom.HashDomain) (K : Key) (s : RegQ) : Prop :=
  ∃ y sel, s.1.1 z = some y ∧ s.2.2.2 K = some sel ∧ sel.1 ≠ z ∧ pairDigest y = sel.2

open scoped Classical in
/-- **The recorded selected weight**: `RecHitQ`. -/
noncomputable def recSWt (z : Qrom.HashDomain) (K : Key) (s : RegQ) : ℝ :=
  if RecHitQ z K s then 1 else 0

/-! ## Sums along the challenge prefix -/

/-- A read weight summed along the challenge prefix (program and record ports: `0`). -/
noncomputable def preTot (pol : DigestPolicy) (A : SAdversary) (θ : TVals)
    (dR : HwRead PairOut Qrom.HashDomain QMem →
      Matrix (Unit × RegQ) (Unit × RegQ) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (runtimeR m0Q).totalWeight .instruments (extWeight (hwCost dR fun _ _ ↦ 0)) (prefixQ pol A θ)
    initQ

/-- The Enc weights along the prefix. -/
noncomputable def encPre (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  preTot pol A θ (trialW (pkQ θ) (encWt (pkQ θ)))

/-- The re-grind weights along the prefix. -/
noncomputable def selPre (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  preTot pol A θ (trialW (pkQ θ) selWt)

/-- The recorded unselected weights along the prefix. -/
noncomputable def recUPre (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  preTot pol A θ (trialW (pkQ θ) recUWt)

/-- The recorded selected hits along the prefix. -/
noncomputable def recSPre (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  preTot pol A θ (trialW (pkQ θ) recSWt)

/-- **The classical costs of the challenge prefix**: the refined read cost (`readCostT`) and the
program flip cost for the event `BadRQ pk hon S`, along the run of `prefixQ pol A θ` (record ports
free). -/
noncomputable def twPQ (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures)
    (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  (runtimeR m0Q).totalWeight .instruments
    (extWeight (hwCost (fun c σ ↦ readCostT (BadRQ pk hon S) c σ)
      fun c σ ↦ flipCost (BadRQ pk hon S) (hwProgKraus c) 0 σ)) (prefixQ pol A θ) initQ

/-! ## The ports of the prefix -/

/-- **The ports the challenge prefix calls**: sponge and record ports; trial reads at an encoding
slot; programs of cells without a target once hardwired (`ExemptCell`). -/
def PortOkQ (pk : PublicKey) (hon : HonestCells) :
    (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr c)) => ∃ z K, slotOf pk z = some (.enc K.1 K.2.1 K.2.2) ∧ c = trialRead z K
  | .inl (.inr c) => ∃ z a, c = .programH z a ∧ ExemptCell pk hon z
  | .inr _ => True

/-- **No hardwired encoding cell.** -/
def EncFree (pk : PublicKey) (s : RegQ) : Prop :=
  ∀ x, (s.2.1.1 x).isSome → ∀ K : Key, slotOf pk x ≠ some (.enc K.1 K.2.1 K.2.2)

/-- **The invariant at the prefix's calls**: the port is `PortOkQ`, the input supported on
`EncFree` registers, with no decompressed `⊥`. -/
def PreInvQ (pk : PublicKey) (hon : HonestCells)
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (τ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ) ℂ) : Prop :=
  PortOkQ pk hon i ∧
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
      m.2) {s | EncFree pk s} τ ∧
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
      m.2) {s | NoBot s} (MatrixMap.conj ((1 : Matrix
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) τ)

/-- **The prefix's calls satisfy `PreInvQ`** (the hypothesis of `twPQ_le`). -/
def PrefixInvQ (pk : PublicKey) (hon : HonestCells) (pol : DigestPolicy) (A : SAdversary)
    (θ : TVals) : Prop :=
  ∃ P : ∀ (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port) (E : QReg),
      Matrix (((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ) × E)
        (((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ) × E) ℂ → Prop,
    (∀ i E σ, P i E σ → PreInvQ pk hon i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m0Q).ForallQueries .instruments P (prefixQ pol A θ) initQ

end Quantum.Qrom.Sphincs

end
