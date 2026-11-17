module

public import Quantum.Qrom.Sphincs.Events
public import Quantum.Qrom.Sphincs.GameReads
public import Quantum.Sphincs.Classify

@[expose] public section

/-!
# leanSPHINCS in the random-oracle model: a win is in the event

A state `s` of the hardwired register at `(Y × Y, HashDomain)` answers the verifier's hash calls
through its union view `unionH s` regrouped: the hash of `x` is the component of the pair at the
cell `hmsgRoute (x, false)` (`regroup hmsgRoute (viewP (unionH s))`), as the read program of
`Quantum.Qrom.Sphincs.GameReads` reads it.

`QTable.honCell S0 v`: the honest cell and digest of each Struct slot of the table. Every cell of
the table is exempt (`exemptCell_cellOf`): a start hardwiring only table cells is outside the
event (`not_mem_badQ_start_table`) and programming a table cell costs nothing
(`flipCost_programH_cellOf_eq_zero`).

`win_imp_badQ`: a forgery that verifies with every hashed cell recorded or hardwired, against a
transcript of honest signatures (`v.signature H`), not returned by the signer, puts the state in
`BadQ v.publicKey (QTable.honCell S0 v) S`, when

* every hardwired honest chain step and FORS leaf has a known input (`HwKnown`, implied by its
  slot being `Public`);
* the memory records the signer's selections (`Records`);
* every hardwired call-0 `H_msg` cell is the digest cell of a signed message holding its honest
  pair (`HwDigests`);
* the coverage set `S` covers the view of every signed message (`hcov`).

The proof is the QRPM's (`Quantum.Sphincs.Classify`) with cells for sponge paths. The accepting
verification runs in `Option` with every hash answered by the union (`verify_optHash`), so the
QRPM's `verify_spec` and its companions read off its calls. Along each walk (`chain_meet`,
`tree_meet`, the FORS trees and the FORS key) the forged walk ends at the honest value, so either
some input differs from the honest cell while its output truncates to the honest digest (Struct),
or the walk starts at the honest value and the honest cell is hardwired (`payload_meet`). The
layers then meet the honest trees from the top (`layer_meet`): a hardwired chain step is known,
hence opened by the selection of its key at or below the forged word, equal by incomparability;
the forged encoding cell is the selected one, or an Enc hit. The FORS key and openings are honest
and each opened FORS leaf cell is hardwired, hence its secret disclosed by a signed message. If
the forged call-0 `H_msg` cell is hardwired, it is a signed message's digest cell with its honest
pair, so the forgery is that message's signature; otherwise its pair's view is covered, a Cov hit.
-/

open OracleComp OracleSpec
open scoped ComplexOrder
open HashSig hiding PublicKey
open HashSig.OverPermutation (sequenceFin walkChain foldPath nodePayload)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (layerSignatures)
open Quantum.Sphincs (Slot Key keyOf msgPos ValPos cpos tpos fpos rootPos Known treeBits LayerOk
  Disclosures Covered)
open Quantum.SufCma (QueriesSatisfy queries trace trace_eq_flatMap)
open Quantum.Qrom.Xmss (romAnswers hashRead honestEval IsHash)
open Common.SufCma (SignerReturnedForgery)

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Sponge

/-! ## Verification in `Option` -/

section Over

variable {n : Type → Type} [Monad n] [LawfulMonad n] (impl : QueryImpl RomOracles n)

theorem simulateQ_otsLeaf (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) :
    simulateQ impl (LeanSphincsOver.otsLeaf hashQ seed l τ e message counter values) =
      LeanSphincsOver.otsLeaf (hashBy impl) seed l τ e message counter values := by
  simp only [LeanSphincsOver.otsLeaf, simulateQ_bind, simulateQ_encode]
  refine bind_congr fun x ↦ ?_
  cases x with
  | none => rfl
  | some encoding =>
    simp only [simulateQ_bind, simulateQ_pure, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
      LeanSphincsOver.recoverChain, simulateQ_chainWalk, LeanSphincsOver.leafHash,
      simulateQ_addressedHash]

theorem simulateQ_treeFold (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (path : ℕ → Digest) (levels : ℕ) (value : Digest) :
    simulateQ impl (LeanSphincsOver.treeFold hashQ seed l τ e path levels value) =
      LeanSphincsOver.treeFold (hashBy impl) seed l τ e path levels value := by
  simp only [LeanSphincsOver.treeFold, Quantum.Sphincs.WithHash.simulateQ_foldPath,
    simulateQ_addressedHash]

theorem simulateQ_forsRecover (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    simulateQ impl (LeanSphincsOver.forsRecover hashQ seed idx leaves opening) =
      LeanSphincsOver.forsRecover (hashBy impl) seed idx leaves opening := by
  simp only [LeanSphincsOver.forsRecover, LeanSphincsOver.forsTreeRecover,
    LeanSphincsOver.forsLeafHash, LeanSphincsOver.forsPublicKey, simulateQ_bind,
    Quantum.Sphincs.WithHash.simulateQ_sequenceFin, Quantum.Sphincs.WithHash.simulateQ_foldPath,
    simulateQ_addressedHash]

theorem simulateQ_messageDigest (pk : PublicKey) (randomizer : Randomizer) (message : Message) :
    simulateQ impl (LeanSphincsOver.messageDigest hashQ pk randomizer message) =
      LeanSphincsOver.messageDigest (hashBy impl) pk randomizer message := by
  simp only [LeanSphincsOver.messageDigest, LeanSphincsOver.messageDigestCall, simulateQ_bind,
    simulateQ_pure, Quantum.Sphincs.WithHash.simulateQ_sequenceFin]
  rfl

theorem simulateQ_verifyLayers (seed : PublicParameter) (idx : Index) (σ : Signature) :
    ∀ (layersLeft : ℕ) (message : Digest),
      simulateQ impl (LeanSphincsOver.verifyLayers hashQ seed idx σ layersLeft message) =
        LeanSphincsOver.verifyLayers (hashBy impl) seed idx σ layersLeft message
  | 0, _ => rfl
  | layersLeft + 1, message => by
    simp only [LeanSphincsOver.verifyLayers]
    split
    · simp only [simulateQ_bind, simulateQ_otsLeaf]
      refine bind_congr fun x ↦ ?_
      cases x with
      | none => rfl
      | some value =>
        simp only [simulateQ_bind, simulateQ_treeFold]
        refine bind_congr fun root ↦ ?_
        split
        · rfl
        · exact simulateQ_verifyLayers seed idx σ layersLeft root
    · rfl

theorem simulateQ_verify (pk : PublicKey) (message : Message) (σ : Signature) :
    simulateQ impl (LeanSphincsOver.verify hashQ pk message σ) =
      LeanSphincsOver.verify (hashBy impl) pk message σ := by
  simp only [LeanSphincsOver.verify, simulateQ_bind, simulateQ_messageDigest,
    simulateQ_forsRecover]
  refine bind_congr fun digest ↦ bind_congr fun forsKey ↦ ?_
  rw [simulateQ_verifyLayers]
  refine bind_congr fun x ↦ ?_
  cases x <;> rfl

end Over

section Copy

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)

/-- The verifier's walk up the hypertree is the QRPM copy's (`Quantum.Sphincs.WithHash`). -/
theorem verifyLayers_eq_withHash (seed : PublicParameter) (idx : Index) (σ : Signature) :
    ∀ (layersLeft : ℕ) (message : Digest),
      LeanSphincsOver.verifyLayers hash seed idx σ layersLeft message =
        Quantum.Sphincs.WithHash.verifyLayers hash seed idx σ layersLeft message
  | 0, _ => rfl
  | layersLeft + 1, message => by
    simp only [LeanSphincsOver.verifyLayers, Quantum.Sphincs.WithHash.verifyLayers]
    by_cases h : layersLeft < layerCount
    · rw [dite_eq_left h, dite_eq_left h]
      refine bind_congr fun x ↦ ?_
      cases x with
      | none => rfl
      | some value =>
        refine bind_congr fun root ↦ ?_
        split
        · rfl
        · exact verifyLayers_eq_withHash seed idx σ layersLeft root
    · rw [dite_eq_right h, dite_eq_right h]

/-- **The verifier is the QRPM copy's.** -/
theorem verify_eq_withHash (pk : PublicKey) (message : Message) (σ : Signature) :
    LeanSphincsOver.verify hash pk message σ =
      Quantum.Sphincs.WithHash.verify hash pk message σ := by
  simp only [LeanSphincsOver.verify, Quantum.Sphincs.WithHash.verify, verifyLayers_eq_withHash]
  rfl

end Copy

/-- **The hash of a union view**: the value of a pair-valued function at a recorded or hardwired
cell, `0` elsewhere. -/
def viewP (U : Qrom.HashDomain → Option (HashOutput × HashOutput)) (x : Qrom.HashDomain) :
    HashOutput × HashOutput :=
  (U x).getD 0

/-- The model's oracles in `Option`: a hash answered by the regrouped union view when its cell is
recorded or hardwired, failing elsewhere; coins fail. -/
def optImpl (U : Qrom.HashDomain → Option (HashOutput × HashOutput)) :
    QueryImpl RomOracles Option
  | .inl _ => none
  | .inr x => (U (hmsgRoute (x, false)).1).map (pairPart (hmsgRoute (x, false)).2)

/-- **The hash answered by a union view**, in `Option`. -/
def optHash (U : Qrom.HashDomain → Option (HashOutput × HashOutput)) :
    HashInput → Option HashOutput :=
  hashBy (optImpl U)

theorem optHash_of_encodeInput {U : Qrom.HashDomain → Option (HashOutput × HashOutput)}
    {input : HashInput} {x : Qrom.HashDomain} (h : encodeInput input = some x) :
    optHash U input = (U (hmsgRoute (x, false)).1).map (pairPart (hmsgRoute (x, false)).2) :=
  hashBy_of_encodeInput_eq_some (optImpl U) h

/-- An input other than a call 1 of `H_msg` is answered by the first component of its own cell. -/
theorem optHash_of_ne_one {U : Qrom.HashDomain → Option (HashOutput × HashOutput)}
    {input : HashInput} {x : Qrom.HashDomain} (h : encodeInput input = some x)
    (h1 : hmsgCall x ≠ some 1) {o : HashOutput} (ho : optHash U input = some o) :
    ∃ ω, U x = some ω ∧ ω.1 = o := by
  rw [optHash_of_encodeInput h, hmsgRoute_of_ne h1] at ho
  obtain ⟨ω, hω, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact ⟨ω, hω, rfl⟩

/-- A hashed point of a computation is in its honest evaluation's reads. -/
theorem mem_honestEval_snd {H : Qrom.HashDomain → HashOutput} {α : Type}
    {x : OracleComp RomOracles α} {c : Qrom.HashDomain}
    (hq : .inr c ∈ queries (romAnswers H) x) : c ∈ (honestEval H x).2 := by
  change c ∈ trace (romAnswers H) hashRead x
  rw [trace_eq_flatMap]
  exact List.mem_flatMap.2 ⟨_, hq, List.mem_singleton_self c⟩

/-- The answer in `Option` at a recorded or hardwired cell is the regrouped union view's. -/
theorem optImpl_inr_eq {U : Qrom.HashDomain → Option (HashOutput × HashOutput)}
    {c : Qrom.HashDomain} {ω : HashOutput × HashOutput} (hω : U (hmsgRoute (c, false)).1 = some ω) :
    optImpl U (.inr c) = some (romAnswers (regroup hmsgRoute (viewP U)) (.inr c)) := by
  have e1 : optImpl U (.inr c) =
      (U (hmsgRoute (c, false)).1).map (pairPart (hmsgRoute (c, false)).2) := rfl
  have e2 : romAnswers (regroup hmsgRoute (viewP U)) (.inr c) =
      pairPart (hmsgRoute (c, false)).2 (viewP U (hmsgRoute (c, false)).1) := rfl
  have e3 : viewP U (hmsgRoute (c, false)).1 = ω := by
    rw [viewP, hω]
    rfl
  rw [e1, e2, e3, hω, Option.map_some]

/-- **Verification through the union view**: an honest evaluation of the verifier against the
regrouped union view that accepts, with every hashed cell recorded or hardwired, accepts in
`Option` with every hash answered by the union. -/
theorem verify_optHash {U : Qrom.HashDomain → Option (HashOutput × HashOutput)} {pk : PublicKey}
    {forgery : Forgery}
    (hv : (honestEval (regroup hmsgRoute (viewP U)) (sphincsRom.verify pk forgery)).1 = true)
    (hr : ∀ c ∈ (honestEval (regroup hmsgRoute (viewP U)) (sphincsRom.verify pk forgery)).2,
      (U (hmsgRoute (c, false)).1).isSome) :
    Quantum.Sphincs.WithHash.verify (optHash U) pk forgery.message forgery.signature =
      some true := by
  have hq : ∀ q ∈ queries (romAnswers (regroup hmsgRoute (viewP U)))
      (sphincsRom.verify pk forgery),
      optImpl U q = some (romAnswers (regroup hmsgRoute (viewP U)) q) := by
    intro q hq
    obtain ⟨c, rfl⟩ := isHash_verify (f := romAnswers (regroup hmsgRoute (viewP U))) pk forgery
      q hq
    obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.1 (hr c (mem_honestEval_snd hq))
    exact optImpl_inr_eq hω
  have h := Quantum.Sphincs.simulateQ_option_eq_some (optImpl U)
    (romAnswers (regroup hmsgRoute (viewP U))) _ hq
  change simulateQ (optImpl U) (LeanSphincsOver.verify hashQ pk forgery.message
    forgery.signature) = _ at h
  rw [simulateQ_verify, verify_eq_withHash] at h
  rw [fst_honestEval] at hv
  exact h.trans (congrArg some hv)

/-! ## Honest cells of the table -/

/-- The Struct positions: chain steps, one-time leaves, hypertree nodes, FORS leaves, FORS nodes
and FORS roots compressions. -/
def RawPos.IsStruct : RawPos → Prop
  | .chain .. | .leaf .. | .node .. | .forsLeaf .. | .forsNode .. | .forsRoots _ => True
  | _ => False

/-- The Struct position of a slot. -/
def slotPos : Slot → Option RawPos
  | .chain l τ e i step => some (.chain l τ e i step)
  | .leaf l τ e => some (.leaf l τ e)
  | .node _ _ 0 _ => none
  | .node l τ (level + 1) index =>
      if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        some (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩)
      else none
  | .forsLeaf idx κ t => some (.forsLeaf idx κ t)
  | .forsNode _ _ 0 _ => none
  | .forsNode idx κ (level + 1) node =>
      if h : level < forsTreeHeight ∧ node < 2 ^ forsTreeHeight then
        some (.forsNode idx κ ⟨level, h.1⟩ ⟨node, h.2⟩)
      else none
  | .forsRoots idx => some (.forsRoots idx)
  | _ => none

/-- **The honest cells of the table**: for a Struct slot of a position in use, the cell of the
position and its digest. -/
def QTable.honCell (S0 : MasterSeed) (v : QTable) (s : Slot) :
    Option (Qrom.HashDomain × Digest) :=
  (slotPos s).bind fun p ↦ if h : p.InRange then some (cellOf S0 ⟨p, h⟩ v, v.dig p) else none

theorem honCell_posSlot (S0 : MasterSeed) (v : QTable) {p : Pos} (hst : p.1.IsStruct) :
    QTable.honCell S0 v (posSlot v p.1) = some (cellOf S0 p v, v.dig p.1) := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | chain l τ e i step =>
    change (some (RawPos.chain l τ e i step)).bind _ = _
    rw [Option.bind_some, dite_eq_left hp]
  | leaf l τ e =>
    change (some (RawPos.leaf l τ e)).bind _ = _
    rw [Option.bind_some, dite_eq_left hp]
  | node l τ level index =>
    change (dite (level.val < layerHeight topLayer ∧ index.val < 2 ^ layerHeight topLayer)
      (fun h ↦ some (RawPos.node l τ ⟨level.val, h.1⟩ ⟨index.val, h.2⟩)) fun _ ↦ none).bind _ = _
    rw [dite_eq_left ⟨level.isLt, index.isLt⟩, Option.bind_some, dite_eq_left hp]
  | forsLeaf idx κ t =>
    change (some (RawPos.forsLeaf idx κ t)).bind _ = _
    rw [Option.bind_some, dite_eq_left hp]
  | forsNode idx κ level node =>
    change (dite (level.val < forsTreeHeight ∧ node.val < 2 ^ forsTreeHeight)
      (fun h ↦ some (RawPos.forsNode idx κ ⟨level.val, h.1⟩ ⟨node.val, h.2⟩)) fun _ ↦ none).bind _
      = _
    rw [dite_eq_left ⟨level.isLt, node.isLt⟩, Option.bind_some, dite_eq_left hp]
  | forsRoots idx =>
    change (some (RawPos.forsRoots idx)).bind _ = _
    rw [Option.bind_some, dite_eq_left hp]
  | _ => exact hst.elim

/-- No position's slot is an encoding slot. -/
theorem posSlot_ne_enc (v : QTable) (p : RawPos) : ∀ l τ e, posSlot v p ≠ .enc l τ e := by
  cases p <;> exact fun _ _ _ h ↦ by cases h

/-- A cell of a cell's slot in range is a call 1 of `H_msg` only at an `H_msg` slot. -/
theorem hmsgCall_cell_ne_one {key : Sphincs.KeyGenerationAndSigning.ExpandedKey} {root : Digest}
    {s : Slot} (hs : SlotInRange s) (hne : ∀ R M c, s ≠ .hmsg R M c) (q : SlotPayload s) :
    hmsgCall (cell key root s q) ≠ some 1 := fun h ↦ by
  obtain ⟨R, M, c, hc⟩ := exists_hmsg_of_hmsgCall hs h
  exact hne R M c hc

/-- A cell determines its payload. -/
theorem cell_payload_inj {key : Sphincs.KeyGenerationAndSigning.ExpandedKey} {root : Digest}
    {s : Slot} (hs : SlotInRange s) {q q' : SlotPayload s}
    (h : cell key root s q = cell key root s q') : q = q' :=
  eq_of_heq (Sigma.mk.inj (cell_injective key root hs hs h)).2

/-- **Every cell of the table is exempt**: once hardwired, it has no Struct or Enc target. -/
theorem exemptCell_cellOf (S0 : MasterSeed) (v : QTable) (p : Pos) :
    ExemptCell v.publicKey (QTable.honCell S0 v) (cellOf S0 p v) := by
  have hsl : slotOf v.publicKey (cellOf S0 p v) = some (posSlot v p.1) :=
    slotOf_cell (v.expandedKey S0) v.root (slotInRange_posSlot v p) _
  by_cases hst : p.1.IsStruct
  · exact exemptCell_honest hsl (posSlot_ne_enc v p.1) (honCell_posSlot S0 v hst)
  · refine exemptCell_of_hon_none hsl (posSlot_ne_enc v p.1) ?_
    obtain ⟨p, _⟩ := p
    cases p <;> first | exact (hst trivial).elim | rfl

/-- **The start is outside the event** when only cells of the table are hardwired. -/
theorem not_mem_badQ_start_table (S0 : MasterSeed) (v : QTable) {S : Disclosures}
    (W₀ : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m₀ : SelMem)
    (h : ∀ x, (W₀.1 x).isSome → ∃ p, cellOf S0 p v = x) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ∉
        BadQ v.publicKey (QTable.honCell S0 v) S :=
  not_mem_badQ_start W₀ m₀ fun x hx ↦ by
    obtain ⟨p, rfl⟩ := h x hx
    exact exemptCell_cellOf S0 v p _ m₀ hx

/-- **Programming a cell of the table costs nothing.** -/
theorem flipCost_programH_cellOf_eq_zero (S0 : MasterSeed) (v : QTable) {S : Disclosures}
    (p : Pos) (y : HashOutput × HashOutput)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQ v.publicKey (QTable.honCell S0 v) S)
      (hwProgKraus (.programH (cellOf S0 p v) y)) 0 σ = 0 :=
  flipCost_programH_badQ_eq_zero (exemptCell_cellOf S0 v p) y hσ

/-! ## Target hits -/

section Hits

variable {pk : PublicKey} {hon : HonestCells} {S : Disclosures}
  {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}

/-- **A Struct hit**: a recorded or hardwired cell at a Struct slot whose pair's digest is the
slot's honest digest, other than the hardwired honest cell. -/
theorem mem_badQ_of_struct {x c : Qrom.HashDomain} {sl : Slot} {d : Digest}
    {ω : HashOutput × HashOutput} (hx : unionH s x = some ω) (hsl : slotOf pk x = some sl)
    (henc : ∀ l τ e, sl ≠ .enc l τ e) (hc : hon sl = some (c, d)) (hd : pairDigest ω = d)
    (hne : ¬(c = x ∧ (s.2.1.1 x).isSome)) : s ∈ BadQ pk hon S := by
  refine ⟨x, ω, hx, .inl ?_⟩
  rw [mem_structTgtQ, tgtDigest, hsl, Option.bind_some, slotDigest_of_ne_enc _ _ _ henc,
    structDigest, hc, Option.bind_some, ite_eq_right hne, hd]

/-- **An Enc hit**: a recorded or hardwired cell at the encoding slot of a selected key, other
than the selected cell, whose pair's digest is the selected digest. -/
theorem mem_badQ_of_enc {x c : Qrom.HashDomain} {K : Key} {d : Digest}
    {ω : HashOutput × HashOutput} (hx : unionH s x = some ω)
    (hsl : slotOf pk x = some (.enc K.1 K.2.1 K.2.2)) (hm : s.2.2 K = some (c, d)) (hne : c ≠ x)
    (hd : pairDigest ω = d) : s ∈ BadQ pk hon S := by
  refine ⟨x, ω, hx, .inl ?_⟩
  rw [mem_structTgtQ, tgtDigest, hsl, Option.bind_some, slotDigest_enc]
  change (s.2.2 K).bind _ = _
  rw [hm, Option.bind_some, ite_eq_right hne, hd]

end Hits

/-! ## Walks meeting the honest table -/

section Meet

variable {S0 : MasterSeed} {v : QTable} {S : Disclosures}
  {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}

/-- **A call at a Struct position's slot reaching its honest digest** (no hit): its payload is the
honest one and the honest cell is hardwired. -/
theorem payload_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {p : Pos}
    (hst : p.1.IsStruct) {q : SlotPayload (posSlot v p.1)} {o : HashOutput}
    (h : optHash (unionH s) (slotInput (v.expandedKey S0) v.root (posSlot v p.1) q) = some o)
    (hd : truncateHash o = v.dig p.1) :
    q = posPayload v p.1 ∧ (s.2.1.1 (cellOf S0 p v)).isSome := by
  have hs := slotInRange_posSlot v p
  have hne : ∀ R M c, posSlot v p.1 ≠ .hmsg R M c := by
    obtain ⟨p, hp⟩ := p
    cases p <;> first | exact hst.elim | exact fun _ _ _ h ↦ by cases h
  obtain ⟨ω, hω, rfl⟩ := optHash_of_ne_one (encodeInput_slotInput _ _ _ q)
    (hmsgCall_cell_ne_one hs hne q) h
  have key : cellOf S0 p v = cell (v.expandedKey S0) v.root (posSlot v p.1) q ∧
      (s.2.1.1 (cell (v.expandedKey S0) v.root (posSlot v p.1) q)).isSome := by
    by_contra hc
    exact hnb (mem_badQ_of_struct hω (slotOf_cell (v.expandedKey S0) v.root hs q)
      (posSlot_ne_enc v p.1) (honCell_posSlot S0 v hst) hd hc)
  exact ⟨(cell_payload_inj hs key.1).symm, key.1 ▸ key.2⟩

/-- **A chain walk ending at the honest chain** (no hit): it starts at the honest value, and the
honest cell of its first step is hardwired. -/
theorem chain_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    (hk : τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l) :
    ∀ (n a : ℕ) (w : Digest), a + n ≤ chainLength - 1 →
      Quantum.Sphincs.WithHash.chainWalk (optHash (unionH s)) v.publicSeed l τ e i a n w =
        some (v.chainValue l τ e i (a + n)) →
      w = v.chainValue l τ e i a ∧ ∀ h : a < chainLength - 1, 0 < n →
        (s.2.1.1 (cellOf S0 ⟨.chain l τ e i ⟨a, h⟩, hk⟩ v)).isSome
  | 0, _, _, _, h => ⟨Option.some.inj h, fun _ h0 ↦ absurd h0 (lt_irrefl 0)⟩
  | n + 1, a, w, han, h => by
    have hlt : a + n < chainLength - 1 := by omega
    obtain ⟨prev, hprev, hstep⟩ := Quantum.Sphincs.walkChain_succ_option hlt h
    obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hstep
    obtain ⟨hp, hw⟩ := payload_meet hnb (p := ⟨.chain l τ e i ⟨a + n, hlt⟩, hk⟩) trivial
      (q := prev) ho (hr.trans (dite_eq_left hlt))
    obtain ⟨hv, hex⟩ := chain_meet hnb hk n a w (by omega) (hp ▸ hprev)
    refine ⟨hv, fun ha _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hw
    · exact hex ha hn

theorem two_pow_layerHeight_le_topLayer (l : Layer) :
    2 ^ layerHeight l ≤ 2 ^ layerHeight topLayer :=
  Quantum.Sphincs.two_pow_layerHeight_le l

/-- **A Merkle path of the hypertree ending at its tree's root** (no hit): it starts at the honest
one-time leaf and its siblings are the honest ones. -/
theorem tree_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l)
    (he : e.val < 2 ^ layerHeight l) {path : ℕ → Digest} {w : Digest}
    (h : Quantum.Sphincs.WithHash.treeFold (optHash (unionH s)) v.publicSeed l τ e path
      (layerHeight l) w = some (v.treeValue l τ (layerHeight l) 0)) :
    w = v.treeValue l τ 0 e.val ∧
      ∀ k < layerHeight l, path k = v.treeValue l τ k (e.val / 2 ^ k ^^^ 1) := by
  have h0 : e.val / 2 ^ layerHeight l = 0 := Nat.div_eq_of_lt he
  have hl := Quantum.Sphincs.layerHeight_le l
  have ht : layerHeight topLayer = 10 := rfl
  refine Quantum.Sphincs.foldPath_meet (node := fun level nodeIndex ↦
      Quantum.Sphincs.WithHash.tweakableHash (optHash (unionH s)) v.publicSeed
        (.node l τ (level + 1) nodeIndex))
    (val := fun k j ↦ v.treeValue l τ k j) (fun k hk a b hab ↦ ?_) (by rw [h0]; exact h)
  have hj : e.val / 2 ^ (k + 1) < 2 ^ (layerHeight l - (k + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he
  have hj' : e.val / 2 ^ (k + 1) < 2 ^ layerHeight topLayer :=
    lt_of_lt_of_le (Quantum.Sphincs.lt_two_pow_of_lt hj) (two_pow_layerHeight_le_topLayer l)
  have hk' : k < layerHeight topLayer := by omega
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hab
  obtain ⟨hp, -⟩ := payload_meet hnb
    (p := ⟨.node l τ ⟨k, hk'⟩ ⟨e.val / 2 ^ (k + 1), hj'⟩, hτ, hk, hj⟩) trivial
    (q := (a, b)) ho (hr.trans (dite_eq_left ⟨hk', hj'⟩))
  exact Prod.mk.inj hp

/-- **A one-time leaf at its honest value** (no hit): the chain ends are the honest ones. -/
theorem leaf_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} (hk : τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l)
    {E : ChainIndex → Digest}
    (h : Quantum.Sphincs.WithHash.leafHash (optHash (unionH s)) v.publicSeed l τ e E =
      some (v.treeValue l τ 0 e.val)) :
    E = v.endpoints l τ e := by
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option h
  have hd : v.treeValue l τ 0 e.val = v.dig (.leaf l τ e) := by
    change v.dig (.leaf l τ (leafOfNat e.val)) = _
    rw [Quantum.Sphincs.leafOfNat_val]
  exact (payload_meet hnb (p := ⟨.leaf l τ e, hk⟩) trivial (q := E) ho (hr.trans hd)).1

/-- **A FORS tree ending at its honest root** (no hit): the opening is the honest secret and path,
and the honest FORS leaf cell is hardwired. -/
theorem forsTree_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {idx : Index}
    {κ : ForsTreeIndex} {t : ForsLeafIndex} {op : ForsTreeOpening} {lf : Digest}
    (hlf : Quantum.Sphincs.WithHash.forsLeafHash (optHash (unionH s)) v.publicSeed idx κ t
      op.secret = some lf)
    (h : foldPath (fun level node ↦ Quantum.Sphincs.WithHash.tweakableHash (optHash (unionH s))
        v.publicSeed (.forsNode idx κ (level + 1) node)) t.val
      (fun level ↦ if h : level < forsTreeHeight then op.path ⟨level, h⟩ else 0) forsTreeHeight lf =
        some (v.forsValue idx κ forsTreeHeight 0)) :
    op.secret = v.forsSecret idx κ t ∧
      (∀ z : Fin forsTreeHeight, op.path z = v.forsValue idx κ z.val ((t.val >>> z.val) ^^^ 1)) ∧
      (s.2.1.1 (cellOf S0 ⟨.forsLeaf idx κ t, trivial⟩ v)).isSome := by
  have hs : t.val < 2 ^ forsTreeHeight := t.isLt
  have h0 : t.val / 2 ^ forsTreeHeight = 0 := Nat.div_eq_of_lt hs
  have key := Quantum.Sphincs.foldPath_meet (node := fun level node ↦
      Quantum.Sphincs.WithHash.tweakableHash (optHash (unionH s)) v.publicSeed
        (.forsNode idx κ (level + 1) node))
    (val := fun k j ↦ v.forsValue idx κ k j) (n := forsTreeHeight) (leaf := t.val)
    (fun k hk a b hab ↦ by
      have hj : t.val / 2 ^ (k + 1) < 2 ^ (forsTreeHeight - (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact hs
      have hj' : t.val / 2 ^ (k + 1) < 2 ^ forsTreeHeight := Quantum.Sphincs.lt_two_pow_of_lt hj
      obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hab
      obtain ⟨hp, -⟩ := payload_meet hnb
        (p := ⟨.forsNode idx κ ⟨k, hk⟩ ⟨t.val / 2 ^ (k + 1), hj'⟩, hj⟩) trivial
        (q := (a, b)) ho (hr.trans (dite_eq_left ⟨hk, hj'⟩))
      exact Prod.mk.inj hp)
    (by rw [h0]; exact h)
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hlf
  have hd : lf = v.dig (.forsLeaf idx κ t) := by
    rw [key.1]
    change v.dig (.forsLeaf idx κ (forsLeafOfNat t.val)) = _
    rw [Quantum.Sphincs.forsLeafOfNat_val]
  obtain ⟨hp, hw⟩ := payload_meet hnb (p := ⟨.forsLeaf idx κ t, trivial⟩) trivial
    (q := op.secret) ho (hr.trans hd)
  refine ⟨hp, fun z ↦ ?_, hw⟩
  have hz := key.2 z.val z.isLt
  simp only [z.isLt, dite_true] at hz
  rw [Nat.shiftRight_eq_div_pow]
  exact hz

/-- **A FORS key at its honest value** (no hit): the roots are the honest ones. -/
theorem forsRoots_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S) {idx : Index}
    {roots : ForsTreeIndex → Digest}
    (h : Quantum.Sphincs.WithHash.forsPublicKey (optHash (unionH s)) v.publicSeed idx roots =
      some (v.forsKey idx)) :
    roots = v.forsRoot idx := by
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option h
  exact (payload_meet hnb (p := ⟨.forsRoots idx, trivial⟩) trivial (q := roots) ho hr).1

end Meet

/-! ## Selections and disclosures -/

section Signed

variable {v : QTable} {H : Qrom.HashDomain → HashOutput}

/-- The selection decodes its digest to its word. -/
theorem decode_of_selectFrom (v : QTable) (H : Qrom.HashDomain → HashOutput) {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {msg : Digest} :
    ∀ attempts counter {sel : EncodingCounter × Encoding},
      v.selectFrom H l τ e msg attempts counter = some sel →
        TargetSum.decodeDigest (v.encDigest H l τ e msg sel.1) = some sel.2
  | 0, _, _, h => by simp [QTable.selectFrom] at h
  | n + 1, counter, sel, h => by
    rw [QTable.selectFrom] at h
    split at h
    · next x hx =>
      obtain rfl := Option.some.inj h
      exact hx
    · exact decode_of_selectFrom v H n (counter + 1) h

theorem decode_of_select {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {msg : Digest}
    {sel : EncodingCounter × Encoding} (h : v.select H l τ e msg = some sel) :
    TargetSum.decodeDigest (v.encDigest H l τ e msg sel.1) = some sel.2 :=
  decode_of_selectFrom v H _ _ h

/-- **The memory records the signer's selections for `message`**: for each layer whose key has a
selection, the cell of its selected encoding input and the selected digest. -/
def Records (v : QTable) (H : Qrom.HashDomain → HashOutput) (m : SelMem) (message : Message) :
    Prop :=
  ∀ l sel, v.layerSelect H (v.index message) l = some sel →
    m (keyOf l (v.index message)) =
      some (encCell v.publicSeed l (treeOfIndex l (v.index message))
          (leafOfIndex l (v.index message)) (v.layerMessage (v.index message) l) sel.1,
        v.encDigest H l (treeOfIndex l (v.index message)) (leafOfIndex l (v.index message))
          (v.layerMessage (v.index message) l) sel.1)

/-- **Every hardwired honest chain step and FORS leaf has a known input**: its input position is
computable from the disclosures (`Known`), as for every `Public` slot. -/
def HwKnown (S0 : MasterSeed) (v : QTable) (H : Qrom.HashDomain → HashOutput)
    (s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) (msgs : List Message) : Prop :=
  (∀ l τ e i (step : ChainStep) (hp : (RawPos.chain l τ e i step).InRange),
    (s.2.1.1 (cellOf S0 ⟨_, hp⟩ v)).isSome →
      Known (v.disclosures H msgs) (cpos l τ e i step.val)) ∧
  ∀ idx κ t, (s.2.1.1 (cellOf S0 ⟨.forsLeaf idx κ t, trivial⟩ v)).isSome →
    Known (v.disclosures H msgs) (.forsSecret idx κ t)

/-- **The hardwired call-0 `H_msg` cells are signed digests**: each is the digest cell of a signed
message and holds its honest pair. -/
def HwDigests (S0 : MasterSeed) (v : QTable)
    (s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) (msgs : List Message) : Prop :=
  ∀ x ω, hmsgCall x = some 0 → s.2.1.1 x = some ω →
    ∃ M ∈ msgs, x = cellOf S0 (digPos M) v ∧ ω = v (digPos M)

/-- The selection of a key depends on the key only. -/
theorem layerSelect_congr {l : Layer} {idx idx' : Index} (h : keyOf l idx' = keyOf l idx) :
    v.layerSelect H idx' l = v.layerSelect H idx l := by
  rw [QTable.layerSelect_eq, QTable.layerSelect_eq, h]
  have h1 : treeOfIndex l idx' = treeOfIndex l idx := congrArg (fun K : Key ↦ K.2.1) h
  have h2 : leafOfIndex l idx' = leafOfIndex l idx := congrArg (fun K : Key ↦ K.2.2) h
  rw [h1, h2]

/-- The value a key signs depends on the key only. -/
theorem layerMessage_congr {l : Layer} {idx idx' : Index} (h : keyOf l idx' = keyOf l idx) :
    v.layerMessage idx' l = v.layerMessage idx l := by
  rw [← QTable.msgPos_eq, ← QTable.msgPos_eq, h]

-- The linter's `whnf` of the disclosure memberships runs the counter search.
set_option linter.constructorNameAsVariable false in
/-- **A disclosed chain position is opened by a signed message's selection of its key.** -/
theorem chain_mem_disclosures {msgs : List Message} {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} {i : ChainIndex} {j : Fin chainLength}
    (h : ValPos.chain l τ e i j ∈ v.disclosures H msgs) :
    ∃ M ∈ msgs, keyOf l (v.index M) = (l, τ, e) ∧
      ∃ sel, v.layerSelect H (v.index M) l = some sel ∧ sel.2 i = j := by
  rcases h with h | h
  · simp [rootPos, tpos] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨M, hM, hd⟩ := h
  refine ⟨M, hM, ?_⟩
  unfold QTable.disclosedBy at hd
  rcases h0 : v.layerSelect H (v.index M) 0 with _ | s0 <;>
    rcases h1 : v.layerSelect H (v.index M) 1 with _ | s1 <;>
    rcases h2 : v.layerSelect H (v.index M) 2 with _ | s2 <;>
    simp only [h0, h1, h2, Set.mem_empty_iff_false] at hd
  rcases hd with ((⟨κ, hd | ⟨z, hd⟩⟩ | ⟨i', hd⟩ | ⟨z, hd⟩) | ⟨i', hd⟩ | ⟨z, hd⟩) |
    ⟨i', hd⟩ | ⟨z, hd⟩
  · cases hd
  · simp [fpos] at hd
  · simp only [cpos, ValPos.chain.injEq] at hd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hd
    exact ⟨rfl, s0, h0, Fin.ext (Nat.mod_eq_of_lt (s0.2 _).isLt).symm⟩
  · simp [tpos] at hd
  · simp only [cpos, ValPos.chain.injEq] at hd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hd
    exact ⟨rfl, s1, h1, Fin.ext (Nat.mod_eq_of_lt (s1.2 _).isLt).symm⟩
  · simp [tpos] at hd
  · simp only [cpos, ValPos.chain.injEq] at hd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hd
    exact ⟨rfl, s2, h2, Fin.ext (Nat.mod_eq_of_lt (s2.2 _).isLt).symm⟩
  · simp [tpos] at hd

set_option linter.constructorNameAsVariable false in
/-- **A disclosed FORS secret is a signed message's leaf.** -/
theorem forsSecret_mem_disclosures {msgs : List Message} {idx : Index} {κ : ForsTreeIndex}
    {t : ForsLeafIndex} (h : ValPos.forsSecret idx κ t ∈ v.disclosures H msgs) :
    ∃ M ∈ msgs, v.index M = idx ∧ v.leaves M κ = t := by
  rcases h with h | h
  · simp [rootPos, tpos] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨M, hM, hd⟩ := h
  refine ⟨M, hM, ?_⟩
  unfold QTable.disclosedBy at hd
  rcases h0 : v.layerSelect H (v.index M) 0 with _ | s0 <;>
    rcases h1 : v.layerSelect H (v.index M) 1 with _ | s1 <;>
    rcases h2 : v.layerSelect H (v.index M) 2 with _ | s2 <;>
    simp only [h0, h1, h2, Set.mem_empty_iff_false] at hd
  rcases hd with ((⟨κ', hd | ⟨z, hd⟩⟩ | ⟨i', hd⟩ | ⟨z, hd⟩) | ⟨i', hd⟩ | ⟨z, hd⟩) |
    ⟨i', hd⟩ | ⟨z, hd⟩
  · simp only [ValPos.forsSecret.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    exact ⟨rfl, rfl⟩
  · simp [fpos] at hd
  · simp [cpos] at hd
  · simp [tpos] at hd
  · simp [cpos] at hd
  · simp [tpos] at hd
  · simp [cpos] at hd
  · simp [tpos] at hd

theorem digestOutput_eq_pairCalls (v : QTable) (message : Message) :
    v.digestOutput message = pairCalls (v (digPos message)) :=
  funext fun _ ↦ rfl

/-- The FORS view of a message's digest cell is its signature's index and leaves. -/
theorem pairView_digPos (v : QTable) (message : Message) :
    pairView (v (digPos message)) = (v.index message, v.leaves message) := by
  rw [pairView, ← digestOutput_eq_pairCalls]
  rfl

end Signed

/-! ## The layers -/

section Layers

variable {S0 : MasterSeed} {v : QTable} {H : Qrom.HashDomain → HashOutput} {S : Disclosures}
  {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem} {msgs : List Message}

set_option linter.constructorNameAsVariable false in
/-- **A layer reaching the honest root of its tree** (no hit): it signs the value its key signs,
and it is the layer signature of the key's selection. The forged word is opened at a chain below
its end (a codeword), whose first step is hardwired, hence known, hence opened by the selection
of the same key at or below the forged position; so the selected word is pointwise below the
forged one, equal to it by incomparability, and the forged encoding cell is the selected one, or
an Enc hit. -/
theorem layer_meet (hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) S)
    (hM : ∀ M ∈ msgs, Records v H s.2.2 M) (hEx : HwKnown S0 v H s msgs) {l : Layer}
    {idx : Index} {σ : Signature} {msg root : Digest}
    (hok : LayerOk (optHash (unionH s)) v.publicSeed idx σ l msg root)
    (hroot : root = v.treeRoot l (treeOfIndex l idx)) :
    msg = v.layerMessage idx l ∧ v.layerSig H idx l = some (σ.layers l) := by
  subst hroot
  have hτ := treeOfIndex_lt l idx
  have he := Quantum.Sphincs.leafOfIndex_lt l idx
  obtain ⟨w, hots, hfold⟩ := hok
  obtain ⟨hw, hpath⟩ := tree_meet hnb hτ he hfold
  obtain ⟨o, x, ho, hx, E, hE, hleaf⟩ := Quantum.Sphincs.otsLeaf_spec hots
  rw [hw] at hleaf
  have hEh := leaf_meet hnb ⟨hτ, he⟩ hleaf
  -- The chains: the forged values are honest, and the steps leaving them hardwired.
  have hchain : ∀ i, (σ.layers l).chainValues i =
      v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (x i).val ∧
      ∀ h : (x i).val < chainLength - 1, (s.2.1.1 (cellOf S0
        ⟨.chain l (treeOfIndex l idx) (leafOfIndex l idx) i ⟨(x i).val, h⟩, hτ, he⟩ v)).isSome := by
    intro i
    have hi := (x i).isLt
    have hEi : Quantum.Sphincs.WithHash.chainWalk (optHash (unionH s)) v.publicSeed l
        (treeOfIndex l idx) (leafOfIndex l idx) i (x i).val (chainLength - 1 - (x i).val)
        ((σ.layers l).chainValues i) = some (v.chainValue l (treeOfIndex l idx)
          (leafOfIndex l idx) i ((x i).val + (chainLength - 1 - (x i).val))) := by
      rw [show (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 by omega]
      exact (hE i).trans (congrArg some (congrFun hEh i))
    obtain ⟨hval, hex⟩ := chain_meet hnb ⟨hτ, he⟩ _ _ _ (by omega) hEi
    exact ⟨hval, fun h ↦ hex h (by omega)⟩
  -- A hardwired step is known: a signed message's selection of the key opened it at or below.
  have hknown : ∀ i, (x i).val < chainLength - 1 →
      ∃ sel, v.layerSelect H idx l = some sel ∧ sel.2 i ≤ x i ∧
        s.2.2 (keyOf l idx) = some (encCell v.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx)
          (v.layerMessage idx l) sel.1, v.encDigest H l (treeOfIndex l idx) (leafOfIndex l idx)
          (v.layerMessage idx l) sel.1) := by
    intro i hi
    obtain ⟨j', hj', hm⟩ := Quantum.Sphincs.known_chain_pos
      (hEx.1 l _ _ i ⟨(x i).val, hi⟩ ⟨hτ, he⟩ ((hchain i).2 hi)) l (treeOfIndex l idx)
      (leafOfIndex l idx) i (x i) (congrArg (ValPos.chain l _ _ i)
        (Fin.ext (Nat.mod_eq_of_lt (x i).isLt)))
    obtain ⟨M, hMm, hkey, sel, hsel, hseli⟩ := chain_mem_disclosures hm
    have hrec := hM M hMm l sel hsel
    rw [layerSelect_congr hkey] at hsel
    have h1 : treeOfIndex l (v.index M) = treeOfIndex l idx := congrArg (fun K : Key ↦ K.2.1) hkey
    have h2 : leafOfIndex l (v.index M) = leafOfIndex l idx := congrArg (fun K : Key ↦ K.2.2) hkey
    rw [layerMessage_congr hkey, h1, h2, hkey] at hrec
    exact ⟨sel, hsel, by rw [hseli]; exact hj', hrec⟩
  have hvx := Quantum.Sphincs.Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Quantum.Sphincs.Codeword.exists_lt_of_sum hvx
  obtain ⟨sel, hS, -, hm2⟩ := hknown i0 hi0
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨sel', hS', hle, -⟩ := hknown i h
      rw [hS] at hS'
      obtain rfl := Option.some.inj hS'
      exact hle
    · rw [Fin.le_def]
      have := (sel.2 i).isLt
      omega
  -- Incomparability: the forged word is the selected one; then the encoding cell is.
  have hdec := decode_of_select (v := v) (H := H) hS
  have hxs : sel.2 = x := Quantum.Sphincs.Codeword.eq_of_le
    (Quantum.Sphincs.Codeword.sum_eq_of_decode hdec) hvx hle
  have hcode := encodeInput_encCell v.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx) msg
    (σ.layers l).counter
  obtain ⟨ω, hω, hω1⟩ := optHash_of_ne_one hcode
    (hmsgCall_cell_ne_one (s := .enc l (treeOfIndex l idx) (leafOfIndex l idx)) trivial
      (fun _ _ _ h ↦ by cases h) _) ho
  have hslot : slotOf v.publicKey (encCell v.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx)
      msg (σ.layers l).counter) = some (.enc l (treeOfIndex l idx) (leafOfIndex l idx)) :=
    slotOf_cell (v.expandedKey S0) v.root (s := .enc l (treeOfIndex l idx) (leafOfIndex l idx))
      trivial (msg, (σ.layers l).counter)
  have hx' : TargetSum.decodeDigest (pairDigest ω) = some x := by
    rw [pairDigest, hω1]
    exact hx
  have hdec' : TargetSum.decodeDigest (v.encDigest H l (treeOfIndex l idx) (leafOfIndex l idx)
      (v.layerMessage idx l) sel.1) = some x := by
    rw [← hxs]
    exact hdec
  have hcell : encCell v.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx)
      (v.layerMessage idx l) sel.1 =
      encCell v.publicSeed l (treeOfIndex l idx) (leafOfIndex l idx) msg (σ.layers l).counter := by
    by_contra hne
    exact hnb (mem_badQ_of_enc (K := keyOf l idx) hω hslot hm2 hne
      (Quantum.Sphincs.Codeword.eq_of_decode hx' hdec'))
  have hpay := cell_payload_inj (key := v.expandedKey S0) (root := v.root)
    (s := .enc l (treeOfIndex l idx) (leafOfIndex l idx)) trivial hcell
  obtain ⟨hmsg, hc⟩ := Prod.mk.inj hpay
  refine ⟨hmsg.symm, ?_⟩
  have h2 : (fun i ↦ v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val) =
      (σ.layers l).chainValues := by
    funext i
    rw [(hchain i).1, hxs]
  have h3 : v.authPath l (treeOfIndex l idx) (leafOfIndex l idx) =
      (σ.layers l).authenticationPath := by
    funext z
    have hz := hpath z.val z.isLt
    rw [Verification.layerPath, dite_eq_left z.isLt] at hz
    rw [QTable.authPath, Nat.shiftRight_eq_div_pow]
    exact hz.symm
  rw [QTable.layerSig, QTable.layerSignature,
    show v.select H l (treeOfIndex l idx) (leafOfIndex l idx) (v.layerMessage idx l) = some sel
      from hS]
  simp only [Option.map_some, Option.some.injEq]
  exact Quantum.Sphincs.layerSignature_ext hc h2 h3

end Layers

/-! ## The classification -/

section Win

/-- **A win is in the event**: a forgery that verifies with every hashed cell recorded or
hardwired, against a transcript of honest signatures and not returned by the signer, puts the
state in `BadQ`, when every hardwired honest chain step and FORS leaf has a known input, the
memory records the signer's selections, every hardwired call-0 `H_msg` cell is a signed message's
digest cell with its honest pair, and `S` covers the view of every signed message. -/
theorem win_imp_badQ (S0 : MasterSeed) (v : QTable) (H : Qrom.HashDomain → HashOutput)
    (S : Disclosures) (s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = v.signature H r.1) (hM : ∀ r ∈ log, Records v H s.2.2 r.1)
    (hEx : HwKnown S0 v H s (log.map Sigma.fst)) (hD : HwDigests S0 v s (log.map Sigma.fst))
    (hcov : ∀ r ∈ log, Covered S (pairView (v (digPos r.1))))
    (hfresh : ¬SignerReturnedForgery id log forgery.message forgery.signature)
    (hverify : (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify v.publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify v.publicKey forgery)).2, (unionH s (hmsgRoute (c, false)).1).isSome) :
    s ∈ BadQ v.publicKey (QTable.honCell S0 v) S := by
  by_contra hnb
  have hM' : ∀ M ∈ log.map Sigma.fst, Records v H s.2.2 M := fun M hM0 ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM0
    exact hM r hr
  obtain ⟨o, ho, fk, hfk, hlay⟩ := Quantum.Sphincs.verify_spec (verify_optHash hverify hreads)
  set σ := forgery.signature
  set M := forgery.message
  -- The two digest calls read the pair of the call-0 cell.
  have hc0 := encodeInput_digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 0
  have hc1 := encodeInput_digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 1
  set x0 := digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 0
  have hx0 : hmsgCall x0 = some 0 := by
    rw [hmsgCall_of_encodeInput_eq_some hc0, hmsgCallOf_messageDigestInput]
  obtain ⟨ω, hω, hω0⟩ := optHash_of_ne_one hc0 (by rw [hx0]; exact fun h ↦ by cases h) (ho 0)
  have hω1 : ω.2 = o 1 := by
    have h1 := ho 1
    rw [optHash_of_encodeInput hc1, hmsgRoute_messageDigestInput _ _ _ _ hc0 hc1, hω,
      Option.map_some] at h1
    exact Option.some.inj h1
  have hop : o = pairCalls ω := funext fun c ↦ by
    rcases Quantum.Sphincs.digestCall_cases c with rfl | rfl
    · rw [pairCalls_zero, hω0]
    · rw [pairCalls_one, hω1]
  rw [hop] at hfk hlay
  set idx := (Quantum.Sphincs.digestView (pairCalls ω)).1
  set lv := (Quantum.Sphincs.digestView (pairCalls ω)).2
  obtain ⟨r0, r1, h0, h1, h2⟩ := Quantum.Sphincs.verifyLayers_spec hlay
  -- The layers, from the top.
  have ht : treeOfIndex 2 idx = 0 := Quantum.Sphincs.treeOfIndex_topLayer idx
  obtain ⟨hm2, hs2⟩ := layer_meet hnb hM' hEx h2 (by rw [ht]; rfl)
  obtain ⟨hm1, hs1⟩ := layer_meet hnb hM' hEx h1 hm2
  obtain ⟨hm0, hs0⟩ := layer_meet hnb hM' hEx h0 hm1
  -- FORS: the roots and the openings are honest, the opened leaf cells hardwired.
  obtain ⟨roots, hroots, hpk⟩ := Quantum.Sphincs.forsRecover_spec hfk
  rw [hm0] at hpk
  have hr := forsRoots_meet hnb hpk
  have hfors : ∀ κ, (σ.forsOpening κ).secret = v.forsSecret idx κ (lv κ) ∧
      (∀ z : Fin forsTreeHeight, (σ.forsOpening κ).path z =
        v.forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)) ∧
      (s.2.1.1 (cellOf S0 ⟨.forsLeaf idx κ (lv κ), trivial⟩ v)).isSome := fun κ ↦ by
    obtain ⟨lf, hlf, hfold⟩ := hroots κ
    rw [hr] at hfold
    exact forsTree_meet hnb hlf hfold
  cases hw0 : s.2.1.1 x0 with
  | some y =>
    -- A signed digest cell: the forgery is that message's signature.
    obtain ⟨M', hM'm, hxM, hyM⟩ := hD x0 y hx0 hw0
    have hωy : ω = y := by
      have h := hω
      change (s.2.1.1 x0).or (s.1.1 x0) = some ω at h
      rw [hw0, Option.some_or] at h
      exact (Option.some.inj h).symm
    obtain ⟨r, hrl, rfl⟩ := List.mem_map.1 hM'm
    have hsl := cell_injective (v.expandedKey S0) v.root (s := .hmsg σ.randomizer M 0)
      (s' := .hmsg (v.randomizer r.1) r.1 0) trivial trivial (p := ()) (p' := ()) hxM
    obtain ⟨hR, hMr, -⟩ := Slot.hmsg.inj (congrArg Sigma.fst hsl)
    have hview := pairView_digPos v r.1
    rw [← hyM, ← hωy] at hview
    have hidx : idx = v.index r.1 := congrArg Prod.fst hview
    have hlv : lv = v.leaves r.1 := congrArg Prod.snd hview
    apply hfresh
    refine ⟨r, hrl, hMr.symm, ?_⟩
    rw [hlog r hrl]
    unfold QTable.signature
    rw [← hidx, hs0, hs1, hs2]
    change some ⟨v.randomizer r.1, v.forsOpening idx (v.leaves r.1),
      layerSignatures (σ.layers 0) (σ.layers 1) (σ.layers 2)⟩ = some σ
    rw [← hlv, Quantum.Sphincs.layerSignatures_layers, ← hR]
    have hop : v.forsOpening idx lv = σ.forsOpening := funext fun κ ↦
      Quantum.Sphincs.forsTreeOpening_ext (hfors κ).1.symm (funext fun z ↦ ((hfors κ).2.1 z).symm)
    rw [hop]
  | none =>
    -- Otherwise the opened leaves are disclosed, hence covered: a Cov hit.
    apply hnb
    refine mem_badQ_of_cov hω hx0 hw0 fun κ ↦ ?_
    have hk := Quantum.Sphincs.known_forsSecret (hEx.2 idx κ (lv κ) (hfors κ).2.2)
    obtain ⟨M', hM'm, hi, hl⟩ := forsSecret_mem_disclosures hk
    obtain ⟨r, hrl, rfl⟩ := List.mem_map.1 hM'm
    have hc := hcov r hrl κ
    rw [pairView_digPos] at hc
    change lv κ ∈ S idx κ
    rw [← hi, ← hl]
    exact hc

end Win

end Quantum.Qrom.Sphincs

end
