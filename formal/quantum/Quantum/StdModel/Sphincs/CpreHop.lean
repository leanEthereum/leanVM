module

public import Quantum.StdModel.Sphincs.Prf
public import Quantum.StdModel.Sphincs.ItsrHop
public import Quantum.StdModel.Sphincs.Build
public import Quantum.StdModel.Sphincs.Trace

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the CPRE hop

The ideal hybrid read through the CPRE decision (`ideal W tab A (cpreDec h)`) is at most the
success of a straight-line reduction `cpreRed W A` (B5) against CPRE with selective WOTS chains and
adaptive FORS leaves (`Props.cpre W cpreChains slotColl`), at every table of a world with fair
coins. The challenger's chain starts are the secrets (`cpreJ_equiv`); the reduction samples the
randomizers.

* `cprePre`: while `PK.seed` is hidden, the reduction builds the public positions of the key
  (`CpreP`: the chain ends by `value j (chainLength - 1)`, the FORS leaves by `value j 1`, the
  leaves, nodes and FORS keys by evaluations of `slotColl`) with `buildDig`, the selection of every
  key by grinding with evaluations at its encoding slot, and opens every chain at and above its
  selected digit (selective openings, before the reveal); then it reveals `PK.seed`. The openings
  above the selected digit add no lower opening.
* `cpreHandler`: the signature of `M` from the built digests, the openings, the world's hash (the
  message digest) and the FORS secrets of the signed leaves, opened adaptively (`value j 0`), only
  when the signature is returned.
* `cprePost`: the forgery's verification trace (`recVerify`), then a chain and position whose
  forged value walks to the built end and either differs from the known value there or has no
  opening at or below it (`cpreGood`, chosen classically).
* At a fixed table the reduction's run is deterministic (`CpreDet`); its kernel collapses onto the
  signer of the ideal table (`cpre_hK`, `cpreInv_step`); on the CPRE event of the forgery's trace
  the judge accepts (`cpre_judge_of_event`): the transcript is valid (`cpre_valid`), a WOTS chain is
  opened at or below a position exactly when the key's selection is (`cpre_opened_inl`), a FORS
  leaf exactly when a returned signature discloses it (`cpre_opened_inr`).
* `ideal_cpre_le`: `ideal W tab A (cpreDec h) ≤ cpreSucc W cpreChains slotColl tab (cpreRed W A)`.
* `isChargeBound_cpreRed`: `A`'s hash calls plus the honest work, and the CPRE queries of the
  reduction's classical code.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (layerSignatures)
open Quantum.Sphincs (Slot Key keyOf msgPos messageDigestInput treeBits)
open Quantum.Qrom.Sphincs (QTable RawPos Pos slotInput SlotPayload SlotInRange digPos)

namespace Quantum.StdModel.Sphincs

/-! ## The reduction -/

/-- The CPRE queries of leanSPHINCS. -/
abbrev CpreQ : Type :=
  Props.CpreQuery CpreJ Slot Slot SlotPayload

/-- The CPRE ports of leanSPHINCS. -/
abbrev CpreS : OracleSpec CpreQ :=
  Props.CpreSpec PublicParameter Slot CpreJ Digest Slot SlotPayload Digest

/-- A FORS leaf: the instance, the tree, the leaf. -/
abbrev CpreFJ : Type :=
  Index × ForsTreeIndex × ForsLeafIndex

/-- What the reduction knows after its setup. -/
structure CpreData where
  /-- The randomizers. -/
  rnd : Message → Digest
  /-- The key's digests at the public positions. -/
  tf : RawPos → Digest
  /-- The selection of every key. -/
  sel : Key → Option (EncodingCounter × Encoding)
  /-- The chain values at and above the selected digits. -/
  opv : Key × ChainIndex × Fin chainLength → Digest
  /-- `PK.seed`. -/
  par : PublicParameter

/-- The public key of the reduction's data. -/
def CpreData.pk (a : CpreData) : PublicKey :=
  ⟨a.par, (ofDig a.tf).root⟩

/-- The reduction's state: its data, the signing transcript, the opened FORS secrets. -/
abbrev CpreSt : Type :=
  CpreData × SignLog × List (CpreFJ × Digest)

/-- The public positions of the key: the chain ends, the leaves, the nodes, the FORS leaves, the
FORS nodes and the FORS keys. -/
def CpreP : RawPos → Prop
  | .chain _ _ _ _ step => step.val = chainLength - 2
  | .leaf .. | .node .. | .forsLeaf .. | .forsNode .. | .forsRoots _ => True
  | _ => False

/-- The public positions computed by an evaluation of `slotColl`. -/
def CpreEval : RawPos → Prop
  | .leaf .. | .node .. | .forsNode .. | .forsRoots _ => True
  | _ => False

/-- A table from a list: `f a` at each `a` of the list, in order, `b` elsewhere. -/
def cpreTab {α β : Type} [DecidableEq α] {ι : Type} {O : OracleSpec.{0, 0} ι} (L : List α)
    (b : β) (f : α → OracleComp O β) : OracleComp O (α → β) :=
  L.foldlM (fun t a ↦ do
    let x ← f a
    pure (Function.update t a x)) fun _ ↦ b

/-- Layer `l` of a signature of index `idx`: the selection, the chain values at its digits, the
path. -/
def cpreLS (a : CpreData) (idx : Index) (l : Layer) : Option (LayerSignature l) :=
  (a.sel (keyOf l idx)).map fun sl ↦
    ⟨sl.1, fun i ↦ a.opv (keyOf l idx, i, sl.2 i),
      (ofDig a.tf).authPath l (treeOfIndex l idx) (leafOfIndex l idx)⟩

/-- The three layers of a signature of index `idx`, when each key has a selection. -/
def cpreLayers (a : CpreData) (idx : Index) : Option ((l : Layer) → LayerSignature l) :=
  match cpreLS a idx 0, cpreLS a idx 1, cpreLS a idx 2 with
  | some b, some m, some t => some (layerSignatures b m t)
  | _, _, _ => none

/-- The signature of `M` at index `idx` and leaves `lv`, the FORS secrets `fs`, the layers. -/
def cpreSigOf (a : CpreData) (M : Message) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (fs : ForsTreeIndex → Digest) (lay : (l : Layer) → LayerSignature l) : Signature :=
  ⟨a.rnd M, fun κ ↦ ⟨fs κ, fun z ↦ (ofDig a.tf).forsValue idx κ z.val
    (((lv κ).val >>> z.val) ^^^ 1)⟩, lay⟩

/-- The message digest of the two `H_msg` outputs. -/
def cpreMd (o0 o1 : HashOutput) : MessageDigest :=
  truncateMessageDigest fun c ↦ if c = 0 then o0 else o1

/-- The recorded inputs with their outputs as a partial hash. -/
def cpreLookup : List HashInput → List HashOutput → HashInput → Option HashOutput
  | x :: xs, o :: os, y => if y = x then some o else cpreLookup xs os y
  | _, _, _ => none

/-- **The reduction's witness condition**: a WOTS chain of a key in use whose forged value walks,
under the trace `H`, to the built end, and either the chain is not opened at or below the position
or the value differs from the opened one there; or a FORS leaf whose secret maps, under `H`, to the
built leaf, differing from every opened secret of that leaf. -/
def cpreGood (a : CpreData) (fl : List (CpreFJ × Digest)) (H : HashInput → Option HashOutput) :
    CpreJ × ℕ × Digest → Prop
  | (.inl (K, i), μ, z) => KeyIn K ∧ ∃ hμ : μ < chainLength - 1,
      Quantum.Sphincs.WithHash.chainWalk H a.par K.1 K.2.1 K.2.2 i μ (chainLength - 1 - μ) z =
        some ((ofDig a.tf).endpoints K.1 K.2.1 K.2.2 i) ∧
      ((¬∃ sl, a.sel K = some sl ∧ (sl.2 i).val ≤ μ) ∨
        z ≠ a.opv (K, i, ⟨μ, Nat.lt_of_lt_of_le hμ (Nat.sub_le _ _)⟩))
  | (.inr (idx, κ, s), μ, z) => μ = 0 ∧
      (∃ o, H (slotInput (pubKey a.par) 0 (.forsLeaf idx κ s) z) = some o ∧
        truncateHash o = (ofDig a.tf).forsValue idx κ 0 s.val) ∧
      ∀ x, ((idx, κ, s), x) ∈ fl → z ≠ x

/-- A default output. -/
def cpreDflt : CpreJ × ℕ × Digest :=
  (.inr (⟨0, Nat.two_pow_pos _⟩, ⟨0, by decide⟩, ⟨0, Nat.two_pow_pos _⟩), 0, 0)

/-- The reduction's output: a witness of `cpreGood` when there is one. -/
noncomputable def cpreOut (a : CpreData) (fl : List (CpreFJ × Digest))
    (H : HashInput → Option HashOutput) : CpreJ × ℕ × Digest :=
  @Classical.epsilon _ ⟨cpreDflt⟩ (cpreGood a fl H)

section Red

variable (W : OracleWorld)

/-- Keccak-256 in the reduction's classical code. -/
noncomputable def cpreHash (l : HashInput) : OracleComp (W.Oracles + CpreS) HashOutput :=
  liftW CpreS (W.hash l)

/-- A value query `value j μ`. -/
def cpreValQ (j : CpreJ) (μ : ℕ) : OracleComp (W.Oracles + CpreS) Digest :=
  portQ W CpreS (.value j μ)

/-- An evaluation query `eval l t m`. -/
def cpreEvQ (l t : Slot) (m : SlotPayload l) : OracleComp (W.Oracles + CpreS) Digest :=
  portQ W CpreS (.eval l t m)

/-- The reveal of `PK.seed`. -/
def cpreRevQ : OracleComp (W.Oracles + CpreS) PublicParameter :=
  portQ W CpreS .reveal

/-- An evaluation of `slotColl` at the slot of a position, the payload read from `t`. -/
def cpreEvalQ (p : RawPos) (t : RawPos → Digest) : OracleComp (W.Oracles + CpreS) Digest :=
  cpreEvQ W (keySlot p) (keySlot p) (keyPayload p t)

/-- The query of a chain step position of the build: the chain end at the last step. -/
def cpreChainAsk (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex)
    (step : ChainStep) : OracleComp (W.Oracles + CpreS) Digest :=
  if step.val = chainLength - 2 then cpreValQ W (.inl ((l, τ, e), i)) (chainLength - 1)
  else pure 0

/-- **The query of a position of the build**: a chain end, a FORS leaf, or an evaluation; nothing
at the other positions. -/
def cpreAsk (p : RawPos) (t : RawPos → Digest) : OracleComp (W.Oracles + CpreS) Digest :=
  match p with
  | .chain l τ e i step => cpreChainAsk W l τ e i step
  | .leaf l τ e => cpreEvalQ W (.leaf l τ e) t
  | .node l τ level index => cpreEvalQ W (.node l τ level index) t
  | .forsLeaf idx κ s => cpreValQ W (.inr (idx, κ, s)) 1
  | .forsNode idx κ level node => cpreEvalQ W (.forsNode idx κ level node) t
  | .forsRoots idx => cpreEvalQ W (.forsRoots idx) t
  | _ => pure 0

/-- The payload of an encoding trial of `K`: the message and counter `c`. -/
def cpreEncPay (K : Key) (m : Digest) (c : ℕ) : SlotPayload (.enc K.1 K.2.1 K.2.2) :=
  ((m, BitVec.ofNat counterBits c) : Digest × EncodingCounter)

/-- The counter search of the key `K` on `m`, by evaluations at its encoding slot. -/
def cpreSelFrom (K : Key) (m : Digest) :
    ℕ → ℕ → OracleComp (W.Oracles + CpreS) (Option (EncodingCounter × Encoding))
  | 0, _ => pure none
  | n + 1, c => do
    let d ← cpreEvQ W (.enc K.1 K.2.1 K.2.2) (.enc K.1 K.2.1 K.2.2) (cpreEncPay K m c)
    match TargetSum.decodeDigest d with
    | some x => pure (some (BitVec.ofNat counterBits c, x))
    | none => cpreSelFrom K m n (c + 1)

/-- Every key. -/
def cpreKeys : List Key :=
  List.finRange layerCount ×ˢ (List.finRange (2 ^ indexBits) ×ˢ
    List.finRange (2 ^ layerHeight topLayer))

/-- Every chain position. -/
def cprePositions : List (Key × ChainIndex × Fin chainLength) :=
  cpreKeys ×ˢ (List.finRange chainCount ×ˢ List.finRange chainLength)

/-- The selection of every key, on the value it signs read from the built digests. -/
noncomputable def cpreSelAll (tf : RawPos → Digest) :
    OracleComp (W.Oracles + CpreS) (Key → Option (EncodingCounter × Encoding)) :=
  cpreTab cpreKeys none fun K ↦
    cpreSelFrom W K ((ofDig tf).valuePos (msgPos K)) encodingAttemptLimit 0

/-- The opening of chain `i` of `K` at `μ` when `μ` is at or above the selected digit. -/
def cpreOpenQ (sel : Key → Option (EncodingCounter × Encoding))
    (x : Key × ChainIndex × Fin chainLength) : OracleComp (W.Oracles + CpreS) Digest :=
  match sel x.1 with
  | some sl => if sl.2 x.2.1 ≤ x.2.2 then cpreValQ W (.inl (x.1, x.2.1)) x.2.2.val else pure 0
  | none => pure 0

/-- The openings of every chain at and above its selected digit. -/
noncomputable def cpreOpenAll (sel : Key → Option (EncodingCounter × Encoding)) :
    OracleComp (W.Oracles + CpreS) (Key × ChainIndex × Fin chainLength → Digest) :=
  cpreTab cprePositions 0 (cpreOpenQ W sel)

/-- The setup's work while `PK.seed` is hidden: the build, the selections, the openings. -/
noncomputable def cpreStage :
    OracleComp (W.Oracles + CpreS) ((RawPos → Digest) ×
      (Key → Option (EncodingCounter × Encoding)) ×
      (Key × ChainIndex × Fin chainLength → Digest)) := do
  let tf ← buildDig (cpreAsk W)
  let sel ← cpreSelAll W tf
  let opv ← cpreOpenAll W sel
  pure (tf, sel, opv)

/-- **The reduction's setup**: uniform randomizers, the hidden-parameter work, the reveal. -/
noncomputable def cprePre : OracleComp (W.Oracles + CpreS) CpreData := do
  let r ← liftW CpreS (Props.sample W (Message → Digest))
  let x ← cpreStage W
  let P ← cpreRevQ W
  pure ⟨r, x.1, x.2.1, x.2.2, P⟩

/-- The FORS secrets of the leaves `lv` of instance `idx`, opened adaptively. -/
noncomputable def cpreForsQ (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    OracleComp (W.Oracles + CpreS) (ForsTreeIndex → Digest) :=
  cpreTab (List.finRange forsTreeCount) 0 fun κ ↦ cpreValQ W (.inr (idx, κ, lv κ)) 0

/-- The signature of `M` at index `idx` and leaves `lv`: none without the layers, else the FORS
secrets opened and recorded. -/
noncomputable def cpreSignIdx (a : CpreData) (sl : SignLog) (fl : List (CpreFJ × Digest))
    (M : Message) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    OracleComp (W.Oracles + CpreS) (Option Signature × CpreSt) :=
  match cpreLayers a idx with
  | none => pure (none, (a, sl ++ [⟨M, none⟩], fl))
  | some lay => do
    let fs ← cpreForsQ W idx lv
    pure (some (cpreSigOf a M idx lv fs lay),
      (a, sl ++ [⟨M, some (cpreSigOf a M idx lv fs lay)⟩],
        fl ++ (List.finRange forsTreeCount).map fun κ ↦ ((idx, κ, lv κ), fs κ)))

/-- **The reduction's signer**: the message digest by the world's hash, then the signature. -/
noncomputable def cpreHandler : HHandler W SignSpec CpreS CpreSt := fun st M ↦ do
  let o0 ← cpreHash W (messageDigestInput (st.1.rnd M) st.1.par (ofDig st.1.tf).root M 0)
  let o1 ← cpreHash W (messageDigestInput (st.1.rnd M) st.1.par (ofDig st.1.tf).root M 1)
  cpreSignIdx W st.1 st.2.1 st.2.2 M (digestIndex (cpreMd o0 o1))
    (digestForsLeaves (cpreMd o0 o1))

/-- **The reduction's output**: the forgery's verification trace, then the witness. -/
noncomputable def cprePost (a : CpreData) (forg : Forgery) (st : CpreSt) :
    OracleComp (W.Oracles + CpreS) (CpreJ × ℕ × Digest) := do
  let rv ← recVerify (cpreHash W) a.pk forg.message forg.signature
  let os ← rv.2.mapM (cpreHash W)
  pure (cpreOut a st.2.2 (cpreLookup rv.2 os))

/-- **The CPRE reduction (B5)**: the adversary run once against the reduction's signer. -/
noncomputable def cpreRed (A : SAdv W) : Props.Adversary W CpreS Unit (CpreJ × ℕ × Digest) :=
  fun _ ↦ slRed W (cprePre W) (fun a ↦ A a.pk) (fun a ↦ (a, [], [])) (cpreHandler W)
    (cprePost W)

end Red

theorem mem_cpreKeys (K : Key) : K ∈ cpreKeys :=
  List.mem_product.2 ⟨List.mem_finRange _,
    List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩⟩

theorem mem_cprePositions (x : Key × ChainIndex × Fin chainLength) : x ∈ cprePositions :=
  List.mem_product.2 ⟨mem_cpreKeys _,
    List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩⟩

attribute [irreducible] cpreKeys cprePositions

/-! ## Deterministic runs at a fixed table -/

section Det

variable {W : OracleWorld} (tab : W.Tab) (ans : (q : CpreQ) → OracleComp W.Oracles (CpreS.Range q))

/-- **A deterministic run at the table**: from every transcript, the program returns a value
satisfying `Px` and appends entries whose queries satisfy `Qq`. -/
def CpreDet (Qq : CpreQ → Prop) {α : Type} (oa : OracleComp (W.Oracles + CpreS) α)
    (Px : α → Prop) : Prop :=
  ∀ log : QueryLog CpreS, ∃ x w, (simulateQ (logImpl tab ans) oa).run log = pure (x, log ++ w) ∧
    Px x ∧ ∀ e ∈ w, Qq e.1

variable {tab ans} {Qq : CpreQ → Prop}

theorem cpreDet_pure {α : Type} {x : α} {Px : α → Prop} (hx : Px x) :
    CpreDet tab ans Qq (pure x) Px :=
  fun log ↦ ⟨x, [], by rw [simulateQ_pure, StateT.run_pure, List.append_nil], hx, by simp⟩

theorem cpreDet_bind {α β : Type} {oa : OracleComp (W.Oracles + CpreS) α}
    {f : α → OracleComp (W.Oracles + CpreS) β} {P₁ : α → Prop} {P₂ : β → Prop}
    (h₁ : CpreDet tab ans Qq oa P₁) (h₂ : ∀ x, P₁ x → CpreDet tab ans Qq (f x) P₂) :
    CpreDet tab ans Qq (oa >>= f) P₂ := by
  intro log
  obtain ⟨x, w₁, e₁, hx, hw₁⟩ := h₁ log
  obtain ⟨y, w₂, e₂, hy, hw₂⟩ := h₂ x hx (log ++ w₁)
  refine ⟨y, w₁ ++ w₂, ?_, hy, fun e he ↦ (List.mem_append.mp he).elim (hw₁ e) (hw₂ e)⟩
  simp only [simulateQ_bind, StateT.run_bind, e₁, pure_bind, e₂, List.append_assoc]

theorem CpreDet.mono {α : Type} {oa : OracleComp (W.Oracles + CpreS) α} {P₁ P₂ : α → Prop}
    {Qq' : CpreQ → Prop} (h : CpreDet tab ans Qq oa P₁) (hP : ∀ x, P₁ x → P₂ x)
    (hQ : ∀ q, Qq q → Qq' q) : CpreDet tab ans Qq' oa P₂ := fun log ↦ by
  obtain ⟨x, w, e, hx, hw⟩ := h log
  exact ⟨x, w, e, hP x hx, fun e he ↦ hQ _ (hw e he)⟩

theorem cpre_run_portQ (q : CpreQ) {v : CpreS.Range q}
    (hv : simulateQ (W.eager tab) (ans q) = pure v) (log : QueryLog CpreS) :
    (simulateQ (logImpl tab ans) (portQ W CpreS q)).run log = pure (v, log ++ [⟨q, v⟩]) := by
  rw [portQ, simulateQ_spec_query, run_logImpl_inr, hv, map_pure]

theorem cpreDet_portQ (q : CpreQ) {v : CpreS.Range q} {Px : CpreS.Range q → Prop}
    (hv : simulateQ (W.eager tab) (ans q) = pure v) (hq : Qq q) (hP : Px v) :
    CpreDet tab ans Qq (portQ W CpreS q) Px := fun log ↦
  ⟨v, [⟨q, v⟩], cpre_run_portQ q hv log, hP,
    fun e he ↦ by rw [List.mem_singleton.mp he]; exact hq⟩

theorem cpreDet_liftW {α : Type} (oa : OracleComp W.Oracles α) {v : α} {Px : α → Prop}
    (hv : simulateQ (W.eager tab) oa = pure v) (hP : Px v) :
    CpreDet tab ans Qq (liftW CpreS oa) Px :=
  fun log ↦ ⟨v, [], by rw [run_simulateQ_logImpl_liftW, hv, map_pure, List.append_nil], hP,
    by simp⟩

theorem cpreDet_hash (l : HashInput) {Px : HashOutput → Prop} (hP : Px (W.hashOf tab l)) :
    CpreDet tab ans Qq (cpreHash W l) Px :=
  cpreDet_liftW _ (W.simulateQ_hash tab l) hP

theorem cpreDet_valQ (j : CpreJ) (μ : ℕ) {v : Digest} {Px : Digest → Prop}
    (hv : simulateQ (W.eager tab) (ans (.value j μ)) = pure v) (hq : Qq (.value j μ))
    (hP : Px v) : CpreDet tab ans Qq (cpreValQ W j μ) Px :=
  cpreDet_portQ _ hv hq hP

theorem cpreDet_evQ (l t : Slot) (m : SlotPayload l) {v : Digest} {Px : Digest → Prop}
    (hv : simulateQ (W.eager tab) (ans (.eval l t m)) = pure v) (hq : Qq (.eval l t m))
    (hP : Px v) : CpreDet tab ans Qq (cpreEvQ W l t m) Px :=
  cpreDet_portQ _ hv hq hP

theorem cpreDet_foldTab {α β : Type} [DecidableEq α] (f : α → OracleComp (W.Oracles + CpreS) β)
    (R : α → β → Prop) : ∀ (L : List α) (t₀ : α → β), (∀ a ∈ L, CpreDet tab ans Qq (f a) (R a)) →
      CpreDet tab ans Qq (L.foldlM (fun t a ↦ do
        let x ← f a
        pure (Function.update t a x)) t₀)
        (fun F ↦ ∀ a, (a ∈ L → R a (F a)) ∧ (a ∉ L → F a = t₀ a))
  | [], t₀, _ => cpreDet_pure fun a ↦ ⟨fun h ↦ by simp at h, fun _ ↦ rfl⟩
  | a :: L, t₀, hf => by
    rw [List.foldlM_cons]
    refine cpreDet_bind (P₁ := fun t ↦ ∃ x, R a x ∧ t = Function.update t₀ a x)
      (cpreDet_bind (hf a List.mem_cons_self) fun x hx ↦ cpreDet_pure ⟨x, hx, rfl⟩)
      fun t ht ↦ ?_
    obtain ⟨x, hx, rfl⟩ := ht
    refine (cpreDet_foldTab f R L _ fun b hb ↦ hf b (List.mem_cons_of_mem a hb)).mono
      (fun F hF b ↦ ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩) fun _ h ↦ h
    · by_cases hbL : b ∈ L
      · exact (hF b).1 hbL
      · have hba : b = a := by
          rcases List.mem_cons.mp hb with h | h
          · exact h
          · exact (hbL h).elim
        subst hba
        rw [(hF b).2 hbL, Function.update_self]
        exact hx
    · have hba : b ≠ a := fun e ↦ hb (e ▸ List.mem_cons_self)
      have hbL : b ∉ L := fun h ↦ hb (List.mem_cons_of_mem a h)
      rw [(hF b).2 hbL, Function.update_of_ne hba]

/-- **A table from a list** satisfies at each listed point what each of its queries returns. -/
theorem cpreDet_tab {α β : Type} [DecidableEq α] (L : List α) (b : β)
    (f : α → OracleComp (W.Oracles + CpreS) β) (R : α → β → Prop)
    (hf : ∀ a ∈ L, CpreDet tab ans Qq (f a) (R a)) :
    CpreDet tab ans Qq (cpreTab L b f) fun F ↦ ∀ a ∈ L, R a (F a) :=
  (cpreDet_foldTab f R L (fun _ ↦ b) hf).mono (fun _ hF a ha ↦ (hF a).1 ha) fun _ h ↦ h

/-- **The build at the table**: when the query of each position returns the target's value given
the target at the lower public positions, the build returns the target on the public
positions. -/
theorem cpreDet_buildDig (ask : RawPos → (RawPos → Digest) → OracleComp (W.Oracles + CpreS) Digest)
    (T : RawPos → Digest) (Pub : RawPos → Prop)
    (hask : ∀ p : Pos, KeyPart p.1 → ∀ t, CpreDet tab ans Qq (ask p.1 t) fun x ↦ Pub p.1 →
      (∀ q : Pos, KeyPart q.1 → Pub q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) → x = T p.1) :
    CpreDet tab ans Qq (buildDig ask) fun tf ↦
      ∀ p : Pos, KeyPart p.1 → Pub p.1 → tf p.1 = T p.1 := by
  suffices key : ∀ L : List Pos, L.Pairwise (fun a b : Pos ↦ a.1.rank ≤ b.1.rank) →
      (∀ p ∈ L, KeyPart p.1) → ∀ t : RawPos → Digest,
        (∀ q : Pos, KeyPart q.1 → Pub q.1 → q ∉ L → t q.1 = T q.1) →
          CpreDet tab ans Qq (L.foldlM (buildStep ask) t)
            fun tf ↦ ∀ q : Pos, KeyPart q.1 → Pub q.1 → tf q.1 = T q.1 from
    key keyOrder pairwise_keyOrder (fun p hp ↦ (mem_keyOrder p).1 hp) _
      fun q hk _ hq ↦ (hq ((mem_keyOrder q).2 hk)).elim
  intro L
  induction L with
  | nil => exact fun _ _ t hinv ↦ cpreDet_pure fun q hk hq ↦ hinv q hk hq (by simp)
  | cons p L ih =>
    intro hL hK t hinv
    rw [List.pairwise_cons] at hL
    have hkp := hK p List.mem_cons_self
    rw [List.foldlM_cons]
    refine cpreDet_bind
      (P₁ := fun t' ↦ ∀ q : Pos, KeyPart q.1 → Pub q.1 → q ∉ L → t' q.1 = T q.1) ?_
      fun t' ht' ↦ ih hL.2 (fun q hq ↦ hK q (List.mem_cons_of_mem p hq)) t' ht'
    refine cpreDet_bind (hask p hkp t) fun d hd ↦ cpreDet_pure fun q hk hq hnot ↦ ?_
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self]
      refine hd hq fun q' hk' hq' hr ↦ hinv q' hk' hq' fun hmem ↦ ?_
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact lt_irrefl _ hr
      · exact absurd (hL.1 q' hmem) (Nat.not_le.2 hr)
    · rw [Function.update_of_ne fun e ↦ hqp (Subtype.ext e)]
      exact hinv q hk hq fun hmem ↦ (List.mem_cons.1 hmem).elim hqp hnot

end Det

/-! ## The honest table of the challenger's chain starts -/

/-- The table of `PK.seed = P`, the chain starts `s` as the secrets, the randomizers `r`. -/
noncomputable abbrev cpreT (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
    (r : Message → Digest) : QTable :=
  digTable h P (s ∘ cpreJ_equiv) r

/-- The step of chain `j` of the CPRE game under `h`. -/
def cpreG (h : HashInput → HashOutput) (P : PublicParameter) (j : CpreJ) (μ : ℕ) (y : Digest) :
    Digest :=
  truncateHash (h (stepLayout P (cpreTweak j μ) y))

section Honest

variable (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
  (r : Message → Digest)

theorem cpreG_inl (K : Key) (i : ChainIndex) {μ : ℕ} (hμ : μ < chainLength - 1) (y : Digest) :
    cpreG h P (.inl (K, i)) μ y = thSlot h P (.chain K.1 K.2.1 K.2.2 i ⟨μ, hμ⟩) y := by
  have hf : (⟨μ % (chainLength - 1), Nat.mod_lt _ (by decide)⟩ : ChainStep) = ⟨μ, hμ⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hμ)
  show truncateHash (h (slotInput (pubKey P) 0
    (.chain K.1 K.2.1 K.2.2 i ⟨μ % (chainLength - 1), Nat.mod_lt _ (by decide)⟩) y)) = _
  rw [hf]
  rfl

theorem cpreG_inr (idx : Index) (κ : ForsTreeIndex) (t : ForsLeafIndex) (μ : ℕ) (y : Digest) :
    cpreG h P (.inr (idx, κ, t)) μ y = thSlot h P (.forsLeaf idx κ t) y :=
  rfl

theorem cpre_chainValue_succ (v : QTable) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) {j : ℕ} (hj : j < chainLength - 1) :
    v.chainValue l τ e i (j + 1) = v.dig (.chain l τ e i ⟨j, hj⟩) := by
  show (if h : j < chainLength - 1 then v.dig (.chain l τ e i ⟨j, h⟩) else 0) = _
  rw [dite_eq_left hj]

theorem cpre_endpoints (v : QTable) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) :
    v.endpoints l τ e i = v.dig (.chain l τ e i ⟨chainLength - 2, by decide⟩) :=
  cpre_chainValue_succ v l τ e i (j := chainLength - 2) (by decide)

/-- A chain step of the honest table is the step of its value below. -/
theorem cpre_dig_chain {K : Key} (hK : KeyIn K) (i : ChainIndex) {j : ℕ}
    (hj : j < chainLength - 1) :
    (cpreT h P s r).dig (.chain K.1 K.2.1 K.2.2 i ⟨j, hj⟩) =
      thSlot h P (.chain K.1 K.2.1 K.2.2 i ⟨j, hj⟩)
        ((cpreT h P s r).chainValue K.1 K.2.1 K.2.2 i j) := by
  refine (dig_digTable_eq_thSlot h P _ r ⟨.chain K.1 K.2.1 K.2.2 i ⟨j, hj⟩, hK⟩ trivial
    id).trans ?_
  show thSlot h P (.chain K.1 K.2.1 K.2.2 i ⟨j, hj⟩)
    ((ofDig (cpreT h P s r).dig).chainValue K.1 K.2.1 K.2.2 i j) = _
  rw [chainValue_congr_key fun q hq _ ↦ dig_ofDig_dig (cpreT h P s r) hq]

/-- **The CPRE walk of a WOTS chain from its start is the honest chain.** -/
theorem cpre_walk_chainValue {K : Key} (hK : KeyIn K) (i : ChainIndex) :
    ∀ μ, μ ≤ chainLength - 1 → walkFwd (cpreG h P (.inl (K, i))) 0 μ (s (.inl (K, i))) =
      (cpreT h P s r).chainValue K.1 K.2.1 K.2.2 i μ
  | 0, _ => (dig_chainStart_digTable h P (s ∘ cpreJ_equiv) r (l := K.1) (τ := K.2.1)
      (e := K.2.2) (i := i) hK).symm
  | μ + 1, hμ => by
    rw [walkFwd_succ, cpre_walk_chainValue hK i μ (by omega), Nat.zero_add,
      cpreG_inl h P K i (by omega), cpre_chainValue_succ _ _ _ _ _ (by omega),
      cpre_dig_chain h P s r hK i (by omega)]

/-- The CPRE walk of a WOTS chain is `walkH` within the chain. -/
theorem cpre_walkFwd_wots (K : Key) (i : ChainIndex) {μ n : ℕ} (hle : μ + n ≤ chainLength - 1)
    (z : Digest) : walkFwd (cpreG h P (.inl (K, i))) μ n z = walkH h P K i μ n z := by
  refine (walkChain_eq_walkFwd _ _ (fun ν hν x ↦ ?_) μ n z hle).symm
  rw [cpreG_inl h P K i hν x]
  rfl

/-- The honest FORS leaf is the leaf hash of the challenger's start. -/
theorem cpre_dig_forsLeaf (idx : Index) (κ : ForsTreeIndex) (t : ForsLeafIndex) :
    (cpreT h P s r).dig (.forsLeaf idx κ t) =
      thSlot h P (.forsLeaf idx κ t) (s (.inr (idx, κ, t))) := by
  refine (dig_digTable_eq_thSlot h P _ r ⟨.forsLeaf idx κ t, trivial⟩ trivial id).trans ?_
  show thSlot h P (.forsLeaf idx κ t) ((ofDig (cpreT h P s r).dig).dig (.forsSecret idx κ t)) = _
  rw [dig_ofDig_dig _ (q := .forsSecret idx κ t) trivial, dig_forsSecret_digTable]
  rfl

theorem cpre_forsSecret (idx : Index) (κ : ForsTreeIndex) (t : ForsLeafIndex) :
    (cpreT h P s r).forsSecret idx κ t = s (.inr (idx, κ, t)) :=
  dig_forsSecret_digTable h P _ r idx κ t

theorem cpre_forsValue_zero (v : QTable) (idx : Index) (κ : ForsTreeIndex) (t : ForsLeafIndex) :
    v.forsValue idx κ 0 t.val = v.dig (.forsLeaf idx κ t) := by
  show v.dig (.forsLeaf idx κ (forsLeafOfNat t.val)) = _
  rw [show forsLeafOfNat t.val = t from Fin.ext (Nat.mod_eq_of_lt t.isLt)]

end Honest

/-! ## Reading only the public positions -/

section PubCongr

variable {v v' : QTable}

theorem cpre_treeValue_congr {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (hd : ∀ q : RawPos, CpreP q → q.rank < 2 + chainLength + level → v.dig q = v'.dig q) :
    v.treeValue l τ level index = v'.treeValue l τ level index := by
  cases level with
  | zero => exact hd (.leaf l τ (leafOfNat index)) trivial (by simp [RawPos.rank])
  | succ level =>
    simp only [QTable.treeValue]
    split_ifs with hl
    · exact hd (.node l τ ⟨level, hl.1⟩ ⟨index, hl.2⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem cpre_forsValue_congr {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hd : ∀ q : RawPos, CpreP q → q.rank < 3 + height → v.dig q = v'.dig q) :
    v.forsValue idx κ height node = v'.forsValue idx κ height node := by
  cases height with
  | zero => exact hd (.forsLeaf idx κ (forsLeafOfNat node)) trivial (by simp [RawPos.rank])
  | succ height =>
    simp only [QTable.forsValue]
    split_ifs with hh
    · exact hd (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem cpre_endpoints_congr {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (hd : ∀ q : RawPos, CpreP q → q.rank < 1 + chainLength → v.dig q = v'.dig q) :
    v.endpoints l τ e = v'.endpoints l τ e := by
  funext i
  rw [cpre_endpoints, cpre_endpoints]
  exact hd _ rfl (by show 2 + (chainLength - 2) < 1 + chainLength; decide)

variable (hd : ∀ q : RawPos, CpreP q → v.dig q = v'.dig q)
include hd

theorem cpre_pub_treeValue : v.treeValue = v'.treeValue := by
  funext l τ level index
  exact cpre_treeValue_congr fun q hq _ ↦ hd q hq

theorem cpre_pub_forsValue : v.forsValue = v'.forsValue := by
  funext idx κ height node
  exact cpre_forsValue_congr fun q hq _ ↦ hd q hq

theorem cpre_pub_endpoints : v.endpoints = v'.endpoints := by
  funext l τ e
  exact cpre_endpoints_congr fun q hq _ ↦ hd q hq

theorem cpre_pub_authPath : v.authPath = v'.authPath := by
  funext l τ e z
  exact congrFun (congrFun (congrFun (congrFun (cpre_pub_treeValue hd) l) τ) z.val) _

theorem cpre_pub_root : v.root = v'.root :=
  congrFun (congrFun (congrFun (congrFun (cpre_pub_treeValue hd) topLayer) 0)
    (layerHeight topLayer)) 0

theorem cpre_pub_keyMsg (K : Key) : v.valuePos (msgPos K) = v'.valuePos (msgPos K) := by
  obtain ⟨l, τ, e⟩ := K
  unfold msgPos
  dsimp only
  split_ifs
  · exact hd _ trivial
  · show v.treeValue _ _ _ _ = v'.treeValue _ _ _ _
    rw [cpre_pub_treeValue hd]

end PubCongr

/-- The payload of a position of an evaluation reads only the public positions below it. -/
theorem cpre_keyPayload_congr (p : RawPos) (hp : CpreEval p) {t t' : RawPos → Digest}
    (ht : ∀ q : Pos, KeyPart q.1 → CpreP q.1 → q.1.rank < p.rank → t q.1 = t' q.1) :
    keyPayload p t = keyPayload p t' := by
  have hd : ∀ q : RawPos, CpreP q → q.rank < p.rank → (ofDig t).dig q = (ofDig t').dig q :=
    fun q hq hr ↦ dig_ofDig_congr fun hin hk ↦ ht ⟨q, hin⟩ hk hq hr
  cases p with
  | leaf l τ e =>
    show (ofDig t).endpoints l τ e = (ofDig t').endpoints l τ e
    exact cpre_endpoints_congr hd
  | node l τ level index =>
    show ((ofDig t).treeValue l τ level.val (2 * index.val),
        (ofDig t).treeValue l τ level.val (2 * index.val + 1)) =
      ((ofDig t').treeValue l τ level.val (2 * index.val),
        (ofDig t').treeValue l τ level.val (2 * index.val + 1))
    exact Prod.ext (cpre_treeValue_congr hd) (cpre_treeValue_congr hd)
  | forsNode idx κ level node =>
    show ((ofDig t).forsValue idx κ level.val (2 * node.val),
        (ofDig t).forsValue idx κ level.val (2 * node.val + 1)) =
      ((ofDig t').forsValue idx κ level.val (2 * node.val),
        (ofDig t').forsValue idx κ level.val (2 * node.val + 1))
    exact Prod.ext (cpre_forsValue_congr hd) (cpre_forsValue_congr hd)
  | forsRoots idx =>
    show (ofDig t).forsRoot idx = (ofDig t').forsRoot idx
    exact funext fun _ ↦ cpre_forsValue_congr hd
  | _ => exact (hp : False).elim

theorem cpreP_keyPart {q : RawPos} (hq : CpreP q) : KeyPart q := by
  cases q <;> simp_all [CpreP, KeyPart]

theorem cpreEval_keyPart {q : RawPos} (hq : CpreEval q) : KeyPart q := by
  cases q <;> simp_all [CpreEval, KeyPart]

theorem cpreEval_not_secret {q : RawPos} (hq : CpreEval q) : ¬IsSecret q := by
  cases q <;> simp_all [CpreEval, IsSecret]

/-- Built digests agreeing on the public positions read as the table there. -/
theorem cpre_dig_ofDig {tf : RawPos → Digest} {v : QTable}
    (htf : ∀ p : Pos, KeyPart p.1 → CpreP p.1 → tf p.1 = v.dig p.1) (q : RawPos) (hq : CpreP q) :
    (ofDig tf).dig q = v.dig q := by
  have hk := cpreP_keyPart hq
  by_cases hin : q.InRange
  · exact (dig_ofDig tf ⟨q, hin⟩ hk).trans (htf ⟨q, hin⟩ hk hq)
  · unfold QTable.dig QTable.out
    rw [dite_eq_right hin, dite_eq_right hin]

/-! ## The CPRE challenger at a fixed table -/

/-- The CPRE challenger's answers for `PK.seed = P` and the chain starts `s`. -/
noncomputable abbrev cpreAns (W : OracleWorld) (P : PublicParameter) (s : CpreJ → Digest) :
    (q : CpreQ) → OracleComp W.Oracles (CpreS.Range q) :=
  (Props.cpre W cpreChains slotColl).answer (P, s)

/-- The rules of the reduction's transcript before the reveal, with the selections `ks`: no
reveal, no evaluation at a step tweak, every opening at or above the selected digit. -/
def CpreQ1 (ks : Key → Option (EncodingCounter × Encoding)) (q : CpreQ) : Prop :=
  q.isReveal = false ∧ (∀ t, q.evalTweak = some t → ¬cpreChains.IsStepTweak t) ∧
    ∀ j ν, q.asValue = some (j, ν) → ν < cpreLen j →
      ∃ K i, j = .inl (K, i) ∧ ∃ sl, ks K = some sl ∧ (sl.2 i).val ≤ ν

/-- The queries of a signing request of `M` under the table `v`: the FORS leaves its returned
signature discloses, opened at `0`. -/
def CpreQ2 (h : HashInput → HashOutput) (v : QTable) (M : Message) (q : CpreQ) : Prop :=
  ∃ j : CpreFJ, q = .value (.inr j) 0 ∧ (v.signature (cellHash h) M).isSome = true ∧
    v.index M = j.1 ∧ v.leaves M j.2.1 = j.2.2

theorem cpreQ1_eval (ks : Key → Option (EncodingCounter × Encoding)) (l t : Slot)
    (m : SlotPayload l) (ht : ∀ j μ, cpreTweak j μ ≠ t) : CpreQ1 ks (.eval l t m) :=
  ⟨rfl, fun t' h ⟨j, μ, _, hj⟩ ↦ ht j μ (hj.trans (Option.some.inj h).symm),
    fun _ _ h ↦ by cases h⟩

theorem cpreQ1_value_end (ks : Key → Option (EncodingCounter × Encoding)) (j : CpreJ) (ν : ℕ)
    (hν : cpreLen j ≤ ν) : CpreQ1 ks (.value j ν) :=
  ⟨rfl, fun _ h ↦ (by cases h), fun j' ν' h hlt ↦ (by cases h; omega)⟩

theorem cpreQ1_open (ks : Key → Option (EncodingCounter × Encoding)) (K : Key) (i : ChainIndex)
    (ν : ℕ) (sl : EncodingCounter × Encoding) (hs : ks K = some sl) (hle : (sl.2 i).val ≤ ν) :
    CpreQ1 ks (.value (.inl (K, i)) ν) :=
  ⟨rfl, fun _ h ↦ (by cases h), fun j ν' h _ ↦ (by cases h; exact ⟨K, i, rfl, sl, hs, hle⟩)⟩

/-- What the reduction's setup computes: the randomizers, `PK.seed`, the table's digests at the
public positions, the selections, the chain values at and above the selected digits. -/
structure CpreDataOk (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
    (r : Message → Digest) (a : CpreData) : Prop where
  rnd : a.rnd = r
  par : a.par = P
  pub : ∀ q, CpreP q → (ofDig a.tf).dig q = (cpreT h P s r).dig q
  sel : ∀ K, a.sel K = keySelect h (cpreT h P s r) K
  opv : ∀ K, KeyIn K → ∀ i (μ : Fin chainLength) sl, a.sel K = some sl → sl.2 i ≤ μ →
    a.opv (K, i, μ) = (cpreT h P s r).chainValue K.1 K.2.1 K.2.2 i μ.val

section Fixed

variable (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (s : CpreJ → Digest)
  (r : Message → Digest)

theorem simulateQ_cpreAns_value (j : CpreJ) (μ : ℕ) :
    simulateQ (W.eager tab) (cpreAns W P s (.value j μ)) =
      pure (walkFwd (cpreG (W.hashOf tab) P j) 0 (min μ (cpreLen j)) (s j)) :=
  simulateQ_walk W tab cpreChains P j 0 _ _

theorem simulateQ_cpreAns_eval (l t : Slot) (m : SlotPayload l) :
    simulateQ (W.eager tab) (cpreAns W P s (.eval l t m)) =
      pure (truncateHash (W.hashOf tab (slotLayout l P t m))) :=
  simulateQ_eval W tab slotColl l P t m

theorem slotLayout_eq (t : Slot) (ht : SlotInRange t) (m : SlotPayload t) :
    slotLayout t P t m = slotInput (pubKey P) 0 t m :=
  slotColl_layout P ht m

/-- An evaluation of the build at the table. -/
theorem cpreDet_evalQ (p : Pos) (hp : CpreEval p.1) (t : RawPos → Digest) :
    CpreDet tab (cpreAns W P s) (CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)))
      (cpreEvalQ W p.1 t) fun x ↦ (∀ q : Pos, KeyPart q.1 → CpreP q.1 → q.1.rank < p.1.rank →
        t q.1 = (cpreT (W.hashOf tab) P s r).dig q.1) →
          x = (cpreT (W.hashOf tab) P s r).dig p.1 := by
  have hne : ∀ M, p.1 ≠ .hmsg M := fun M h ↦ by rw [h] at hp; exact hp
  refine cpreDet_evQ _ _ _ (simulateQ_cpreAns_eval W tab P s _ _ _) (cpreQ1_eval _ _ _ _ ?_)
    fun ht ↦ ?_
  · obtain ⟨p, hin⟩ := p
    cases p <;> first | exact (hp : False).elim |
      (rintro (⟨K, i⟩ | ⟨idx, κ, s'⟩) μ hh <;> cases hh)
  · rw [slotLayout_eq P _ (slotInRange_keySlot p hne)]
    refine (congrArg (thSlot (W.hashOf tab) P (keySlot p.1))
      (cpre_keyPayload_congr p.1 hp ht)).trans ?_
    exact (dig_digTable_eq_thSlot _ P _ r p (cpreEval_keyPart hp)
      (cpreEval_not_secret hp)).symm

/-- **The query of a position of the build at the table.** -/
theorem cpreDet_ask (p : Pos) (t : RawPos → Digest) :
    CpreDet tab (cpreAns W P s) (CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)))
      (cpreAsk W p.1 t) fun x ↦ CpreP p.1 → (∀ q : Pos, KeyPart q.1 → CpreP q.1 →
        q.1.rank < p.1.rank → t q.1 = (cpreT (W.hashOf tab) P s r).dig q.1) →
          x = (cpreT (W.hashOf tab) P s r).dig p.1 := by
  obtain ⟨p, hin⟩ := p
  cases p
  case chain l τ e i step =>
    show CpreDet _ _ _ (cpreChainAsk W l τ e i step) _
    unfold cpreChainAsk
    by_cases hs : step.val = chainLength - 2
    · rw [ite_eq_left hs]
      refine cpreDet_valQ _ _ (simulateQ_cpreAns_value W tab P s _ _)
        (cpreQ1_value_end _ _ _ le_rfl) fun _ _ ↦ ?_
      have hstep : step = ⟨chainLength - 2, by decide⟩ := Fin.ext hs
      subst hstep
      show walkFwd _ 0 (min (chainLength - 1) (chainLength - 1)) _ = _
      rw [min_self, cpre_walk_chainValue (W.hashOf tab) P s r (K := (l, τ, e)) hin i _ le_rfl]
      exact cpre_endpoints _ l τ e i
    · rw [ite_eq_right hs]
      exact cpreDet_pure fun hP ↦ (hs hP).elim
  case leaf l τ e =>
    exact (cpreDet_evalQ W tab P s r ⟨.leaf l τ e, hin⟩ trivial t).mono
      (fun _ hx _ ht ↦ hx ht) fun _ h ↦ h
  case node l τ level index =>
    exact (cpreDet_evalQ W tab P s r ⟨.node l τ level index, hin⟩ trivial t).mono
      (fun _ hx _ ht ↦ hx ht) fun _ h ↦ h
  case forsNode idx κ level node =>
    exact (cpreDet_evalQ W tab P s r ⟨.forsNode idx κ level node, hin⟩ trivial t).mono
      (fun _ hx _ ht ↦ hx ht) fun _ h ↦ h
  case forsRoots idx =>
    exact (cpreDet_evalQ W tab P s r ⟨.forsRoots idx, hin⟩ trivial t).mono
      (fun _ hx _ ht ↦ hx ht) fun _ h ↦ h
  case forsLeaf idx κ t' =>
    refine cpreDet_valQ _ _ (simulateQ_cpreAns_value W tab P s _ _)
      (cpreQ1_value_end _ _ _ le_rfl) fun _ _ ↦ ?_
    exact (cpre_dig_forsLeaf (W.hashOf tab) P s r idx κ t').symm
  all_goals exact cpreDet_pure fun hP ↦ (hP : False).elim

/-- **The counter search at the table** is the table's counter search. -/
theorem cpreDet_selFrom (ks : Key → Option (EncodingCounter × Encoding)) (K : Key) (m : Digest) :
    ∀ n c, CpreDet tab (cpreAns W P s) (CpreQ1 ks) (cpreSelFrom W K m n c)
      (· = (cpreT (W.hashOf tab) P s r).selectFrom (cellHash (W.hashOf tab)) K.1 K.2.1 K.2.2 m n c)
  | 0, _ => cpreDet_pure rfl
  | n + 1, c => by
    rw [cpreSelFrom]
    refine cpreDet_bind (cpreDet_evQ (Px := (· = truncateHash (W.hashOf tab (slotLayout
      (.enc K.1 K.2.1 K.2.2) P (.enc K.1 K.2.1 K.2.2) (cpreEncPay K m c))))) _ _ _
      (simulateQ_cpreAns_eval W tab P s _ _ _) (cpreQ1_eval _ _ _ _ ?_) rfl) fun d hd ↦ ?_
    · rintro (⟨K', i⟩ | ⟨idx, κ, s'⟩) μ hh <;> cases hh
    · subst hd
      have he : truncateHash (W.hashOf tab (slotLayout (.enc K.1 K.2.1 K.2.2) P
          (.enc K.1 K.2.1 K.2.2) (cpreEncPay K m c))) =
          (cpreT (W.hashOf tab) P s r).encDigest (cellHash (W.hashOf tab)) K.1 K.2.1 K.2.2 m
            (BitVec.ofNat counterBits c) := by
        rw [slotLayout_eq P (.enc K.1 K.2.1 K.2.2) trivial, encDigest_cellHash,
          publicSeed_digTable]
        rfl
      simp only [he]
      cases hx : TargetSum.decodeDigest ((cpreT (W.hashOf tab) P s r).encDigest
          (cellHash (W.hashOf tab)) K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c)) with
      | some x =>
        rw [selectFrom_succ_of_some hx]
        exact cpreDet_pure rfl
      | none =>
        rw [selectFrom_succ_of_none hx]
        exact cpreDet_selFrom ks K m n (c + 1)

/-- An opening of the setup at the table. -/
theorem cpreDet_openQ (sel : Key → Option (EncodingCounter × Encoding))
    (hsel : ∀ K, sel K = keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r) K)
    (x : Key × ChainIndex × Fin chainLength) :
    CpreDet tab (cpreAns W P s) (CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)))
      (cpreOpenQ W sel x) fun v ↦ ∀ sl, sel x.1 = some sl → sl.2 x.2.1 ≤ x.2.2 →
        v = walkFwd (cpreG (W.hashOf tab) P (.inl (x.1, x.2.1))) 0 x.2.2.val
          (s (.inl (x.1, x.2.1))) := by
  unfold cpreOpenQ
  cases hsx : sel x.1 with
  | none => exact cpreDet_pure fun sl h ↦ by cases h
  | some sl =>
    dsimp only
    by_cases hle : sl.2 x.2.1 ≤ x.2.2
    · rw [ite_eq_left hle]
      refine cpreDet_valQ _ _ (simulateQ_cpreAns_value W tab P s _ _)
        (cpreQ1_open _ x.1 x.2.1 _ sl ((hsel x.1).symm.trans hsx) hle) fun _ _ _ ↦ ?_
      show walkFwd _ 0 (min x.2.2.val (chainLength - 1)) _ = _
      rw [Nat.min_eq_left (by have := x.2.2.isLt; omega)]
    · rw [ite_eq_right hle]
      refine cpreDet_pure fun sl' h hle' ↦ ?_
      cases h
      exact (hle hle').elim

/-- **The setup's work at the table**: the table's digests on the public positions, the table's
selections, the honest chain values at and above the selected digits. -/
theorem cpreDet_stage :
    CpreDet tab (cpreAns W P s) (CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)))
      (cpreStage W) fun x ↦
        (∀ p : Pos, KeyPart p.1 → CpreP p.1 → x.1 p.1 = (cpreT (W.hashOf tab) P s r).dig p.1) ∧
        (∀ K, x.2.1 K = keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r) K) ∧
        ∀ K i (μ : Fin chainLength) sl, x.2.1 K = some sl → sl.2 i ≤ μ →
          x.2.2 (K, i, μ) = walkFwd (cpreG (W.hashOf tab) P (.inl (K, i))) 0 μ.val
            (s (.inl (K, i))) := by
  unfold cpreStage
  refine cpreDet_bind (cpreDet_buildDig (cpreAsk W) _ CpreP fun p _ t ↦
    cpreDet_ask W tab P s r p t) fun tf htf ↦ ?_
  have hpub := cpre_dig_ofDig htf
  refine cpreDet_bind (cpreDet_tab _ none _
    (fun K v ↦ v = keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r) K) fun K _ ↦
      (cpreDet_selFrom W tab P s r _ K _ encodingAttemptLimit 0).mono (fun v hv ↦ ?_)
        fun _ h ↦ h) fun sel hsel ↦ ?_
  · rw [hv, cpre_pub_keyMsg hpub K]
    rfl
  have hsel' : ∀ K, sel K = keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r) K :=
    fun K ↦ hsel K (mem_cpreKeys K)
  refine cpreDet_bind (cpreDet_tab _ 0 _ _ fun x _ ↦ cpreDet_openQ W tab P s r sel hsel' x)
    fun opv hopv ↦ cpreDet_pure ⟨htf, hsel', fun K i μ sl hs hle ↦
      hopv (K, i, μ) (mem_cprePositions _) sl hs hle⟩

end Fixed

/-! ## The signer of the reduction -/

section Sign

variable {h : HashInput → HashOutput} {P : PublicParameter} {s : CpreJ → Digest}
  {r : Message → Digest} {d0 : CpreData}

theorem cpre_pk_eq (hd : CpreDataOk h P s r d0) : d0.pk = (cpreT h P s r).publicKey := by
  show (⟨d0.par, (ofDig d0.tf).root⟩ : PublicKey) =
    ⟨(cpreT h P s r).publicSeed, (cpreT h P s r).root⟩
  rw [hd.par, publicSeed_digTable, cpre_pub_root hd.pub]

/-- The message digest of the reduction is the table's. -/
theorem cpre_md_eq (hd : CpreDataOk h P s r d0) (M : Message) :
    cpreMd (h (messageDigestInput (d0.rnd M) d0.par (ofDig d0.tf).root M 0))
      (h (messageDigestInput (d0.rnd M) d0.par (ofDig d0.tf).root M 1)) =
      (cpreT h P s r).messageDigest M := by
  have hR : d0.rnd M = (cpreT h P s r).randomizer M := by rw [hd.rnd, randomizer_digTable]
  have hP : d0.par = (cpreT h P s r).publicSeed := by rw [hd.par, publicSeed_digTable]
  rw [hR, hP, cpre_pub_root hd.pub]
  unfold cpreMd QTable.messageDigest QTable.digestOutput
  congr 1
  funext c
  split_ifs
  · exact ((honest_digTable h P _ r).out (digPos M) id).symm
  · exact ((honest_digTable h P _ r).call1 M).symm

/-- Each layer of the reduction's signature is the table's. -/
theorem cpre_layerSig_eq (hd : CpreDataOk h P s r d0) (idx : Index) (l : Layer) :
    cpreLS d0 idx l = (cpreT h P s r).layerSig (cellHash h) idx l := by
  have hK : KeyIn (keyOf l idx) :=
    ⟨Quantum.Qrom.Sphincs.treeOfIndex_lt l idx, Quantum.Sphincs.leafOfIndex_lt l idx⟩
  rw [QTable.layerSig_eq]
  unfold cpreLS QTable.layerSignature
  rw [hd.sel]
  change Option.map _ (keySelect h (cpreT h P s r) (keyOf l idx)) =
    Option.map _ (keySelect h (cpreT h P s r) (keyOf l idx))
  have h1 : ∀ sl : EncodingCounter × Encoding, keySelect h (cpreT h P s r) (keyOf l idx) = some sl →
      (fun i ↦ d0.opv (keyOf l idx, i, sl.2 i)) = fun i ↦
        (cpreT h P s r).chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (sl.2 i).val :=
    fun sl hs ↦ funext fun i ↦ hd.opv _ hK i (sl.2 i) sl ((hd.sel _).trans hs) le_rfl
  have h2 := cpre_pub_authPath hd.pub
  cases hs : keySelect h (cpreT h P s r) (keyOf l idx) with
  | none => rfl
  | some sl =>
    simp only [Option.map_some, Option.some.injEq]
    rw [h1 sl hs, h2]

/-- **The table's signature** from the reduction's layers. -/
theorem cpre_signature_eq (hd : CpreDataOk h P s r d0) (M : Message) :
    (cpreT h P s r).signature (cellHash h) M =
      (cpreLayers d0 ((cpreT h P s r).index M)).map fun lay ↦
        ⟨(cpreT h P s r).randomizer M, (cpreT h P s r).forsOpening ((cpreT h P s r).index M)
          ((cpreT h P s r).leaves M), lay⟩ := by
  unfold QTable.signature cpreLayers
  rw [← cpre_layerSig_eq hd, ← cpre_layerSig_eq hd, ← cpre_layerSig_eq hd]
  cases cpreLS d0 ((cpreT h P s r).index M) 0 <;>
    cases cpreLS d0 ((cpreT h P s r).index M) 1 <;>
      cases cpreLS d0 ((cpreT h P s r).index M) 2 <;> rfl

theorem cpre_sigOf_eq (hd : CpreDataOk h P s r d0) (M : Message) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (fs : ForsTreeIndex → Digest)
    (lay : (l : Layer) → LayerSignature l) (hfs : ∀ κ, fs κ = s (.inr (idx, κ, lv κ))) :
    cpreSigOf d0 M idx lv fs lay =
      ⟨(cpreT h P s r).randomizer M, (cpreT h P s r).forsOpening idx lv, lay⟩ := by
  unfold cpreSigOf QTable.forsOpening
  rw [hd.rnd, randomizer_digTable, cpre_pub_forsValue hd.pub]
  congr 1
  funext κ
  rw [hfs κ, cpre_forsSecret]

theorem cpre_logMsgs_append (sl : SignLog) (M : Message) (x : Option Signature) :
    logMsgs (sl ++ [⟨M, x⟩]) = logMsgs sl ++ [M] := by
  simp [logMsgs, logPairs]

theorem cpre_forsOpened_append {v : QTable} {l : List Message} (l' : List Message)
    {idx : Index} {κ : ForsTreeIndex} {t : ForsLeafIndex} (ho : ForsOpened h v l idx κ t) :
    ForsOpened h v (l ++ l') idx κ t := by
  obtain ⟨M, hM, hs⟩ := ho
  exact ⟨M, List.mem_append_left _ hM, hs⟩

end Sign

/-! ## The invariant of the reduction's run -/

/-- **The invariant**: the setup's data; the transcript is the setup's, the reveal, then FORS
openings of disclosed leaves; the recorded FORS secrets are exactly the disclosed leaves'. -/
def CpreInv (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
    (r : Message → Digest) (d0 : CpreData) (w1 : QueryLog CpreS)
    (p : CpreSt × QueryLog CpreS) : Prop :=
  p.1.1 = d0 ∧
    (∃ w2 : QueryLog CpreS, p.2 = w1 ++ ⟨.reveal, P⟩ :: w2 ∧ ∀ e ∈ w2, ∃ j : CpreFJ,
      e.1 = .value (.inr j) 0 ∧ ForsOpened h (cpreT h P s r) (logMsgs p.1.2.1) j.1 j.2.1 j.2.2) ∧
    (∀ j y, (j, y) ∈ p.1.2.2 →
      y = s (.inr j) ∧ ForsOpened h (cpreT h P s r) (logMsgs p.1.2.1) j.1 j.2.1 j.2.2) ∧
    ∀ j : CpreFJ, ForsOpened h (cpreT h P s r) (logMsgs p.1.2.1) j.1 j.2.1 j.2.2 →
      (j, s (.inr j)) ∈ p.1.2.2

theorem cpreInv_init (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
    (r : Message → Digest) (d0 : CpreData) (w1 : QueryLog CpreS) :
    CpreInv h P s r d0 w1 ((d0, [], []), w1 ++ [⟨.reveal, P⟩]) := by
  refine ⟨rfl, ⟨[], rfl, by simp⟩, by simp, fun j hj ↦ ?_⟩
  obtain ⟨M, hM, -⟩ := hj
  simp [logMsgs, logPairs] at hM

/-- The CPRE judge's condition on the transcript and the output. -/
def cpreJudgeP (h : HashInput → HashOutput) (P : PublicParameter) (s : CpreJ → Digest)
    (log : QueryLog CpreS) (out : CpreJ × ℕ × Digest) : Prop :=
  Props.CpreValid cpreChains log ∧ out.2.1 < cpreLen out.1 ∧
    walkFwd (cpreG h P out.1) out.2.1 (cpreLen out.1 - out.2.1) out.2.2 =
      walkFwd (cpreG h P out.1) 0 (cpreLen out.1) (s out.1) ∧
    (out.2.2 ≠ walkFwd (cpreG h P out.1) 0 out.2.1 (s out.1) ∨
      ¬Props.OpenedAtOrBelow log out.1 out.2.1)

/-- The reduction's game decision on its run. -/
noncomputable def cpreDRed (h : HashInput → HashOutput) (P : PublicParameter)
    (s : CpreJ → Digest) (d0 : CpreData) (x : Forgery × (CpreSt × QueryLog CpreS)) : Bool :=
  Props.holds (cpreJudgeP h P s x.2.2
    (cpreOut d0 x.2.1.2.2 (Extract.traceH h d0.pk x.1.message x.1.signature)))

theorem cpre_dropWhile_append {α : Type} (p : α → Bool) (l₂ : List α) :
    ∀ l₁ : List α, (∀ a ∈ l₁, p a = true) → (l₁ ++ l₂).dropWhile p = l₂.dropWhile p
  | [], _ => rfl
  | a :: l, h => by
    rw [List.cons_append, List.dropWhile_cons_of_pos (h a List.mem_cons_self)]
    exact cpre_dropWhile_append p l₂ l fun b hb ↦ h b (List.mem_cons_of_mem a hb)

/-! ## The transcript -/

section Transcript

variable {ks : Key → Option (EncodingCounter × Encoding)} {w1 w2 : QueryLog CpreS}
  (P : PublicParameter) (hw1 : ∀ e ∈ w1, CpreQ1 ks e.1)
  (hw2 : ∀ e ∈ w2, ∃ j : CpreFJ, e.1 = .value (.inr j) 0)
include hw1 hw2

/-- **The reduction's transcript is valid.** -/
theorem cpre_valid : Props.CpreValid cpreChains (w1 ++ ⟨.reveal, P⟩ :: w2) := by
  refine ⟨fun t ht ↦ ?_, fun e he jμ hjμ _ ↦ ?_⟩
  · obtain ⟨e, he, het⟩ := List.mem_filterMap.mp ht
    rcases List.mem_append.mp he with he | he
    · exact (hw1 e he).2.1 t het
    · rcases List.mem_cons.mp he with rfl | he
      · cases het
      · obtain ⟨j, hj⟩ := hw2 e he
        rw [hj] at het
        cases het
  · have hp : Props.phaseTwo (fun q ↦ q.isReveal) (w1 ++ ⟨.reveal, P⟩ :: w2) =
        ⟨.reveal, P⟩ :: w2 :=
      (cpre_dropWhile_append (fun e : (q : CpreQ) × CpreS.Range q ↦ !e.1.isReveal) _ w1
        fun e he ↦ by simp [(hw1 e he).1]).trans rfl
    rw [hp] at he
    rcases List.mem_cons.mp he with rfl | he
    · cases hjμ
    · obtain ⟨j, hj⟩ := hw2 e he
      rw [hj] at hjμ
      cases hjμ
      rfl

/-- A WOTS chain is opened at or below `μ` only at or above its selected digit. -/
theorem cpre_opened_inl {K : Key} {i : ChainIndex} {μ : ℕ} (hμ : μ < chainLength - 1)
    (hO : Props.OpenedAtOrBelow (w1 ++ ⟨.reveal, P⟩ :: w2) (.inl (K, i)) μ) :
    ∃ sl, ks K = some sl ∧ (sl.2 i).val ≤ μ := by
  obtain ⟨ν, hν, hmem⟩ := hO
  obtain ⟨e, he, hev⟩ := List.mem_filterMap.mp hmem
  rcases List.mem_append.mp he with he | he
  · obtain ⟨K', i', hj, sl, hs, hle⟩ :=
      (hw1 e he).2.2 _ _ hev (show ν < chainLength - 1 by omega)
    cases hj
    exact ⟨sl, hs, hle.trans hν⟩
  · rcases List.mem_cons.mp he with rfl | he
    · cases hev
    · obtain ⟨j, hj⟩ := hw2 e he
      rw [hj] at hev
      cases hev

/-- A FORS leaf is opened only by an opening after the reveal. -/
theorem cpre_opened_inr {j : CpreFJ}
    (hO : Props.OpenedAtOrBelow (w1 ++ ⟨.reveal, P⟩ :: w2) (.inr j) 0) :
    ∃ e ∈ w2, e.1 = .value (.inr j) 0 := by
  obtain ⟨ν, hν, hmem⟩ := hO
  obtain ⟨e, he, hev⟩ := List.mem_filterMap.mp hmem
  rcases List.mem_append.mp he with he | he
  · obtain ⟨K', i', hj, -⟩ := (hw1 e he).2.2 _ _ hev (show ν < 1 by omega)
    cases hj
  · rcases List.mem_cons.mp he with rfl | he
    · cases hev
    · obtain ⟨j', hj'⟩ := hw2 e he
      rw [hj'] at hev
      cases hev
      exact ⟨e, he, hj'⟩

end Transcript

/-! ## The judge on the event -/

section Judge

variable {h : HashInput → HashOutput} {P : PublicParameter} {s : CpreJ → Digest}
  {r : Message → Digest} {d0 : CpreData} {w1 : QueryLog CpreS}

/-- **The CPRE event of the trace has a witness** of the reduction's condition. -/
theorem cpre_exists_good (hd : CpreDataOk h P s r d0) {p : CpreSt × QueryLog CpreS}
    (hI : CpreInv h P s r d0 w1 p) {H : HashInput → Option HashOutput}
    (hev : EvCpreT h (cpreT h P s r) H (logMsgs p.1.2.1)) : ∃ w, cpreGood d0 p.1.2.2 H w := by
  obtain ⟨-, -, hfl1, -⟩ := hI
  rcases hev with ⟨K, hK, i, μ, hμ, z, hw, hz⟩ | ⟨idx, κ, t, z, o, ho, hdo, hz⟩
  · refine ⟨(.inl (K, i), μ, z), hK, hμ, ?_, ?_⟩
    · rw [hd.par, cpre_pub_endpoints hd.pub]
      rwa [publicSeed_digTable] at hw
    · by_cases hop : ∃ sl, d0.sel K = some sl ∧ (sl.2 i).val ≤ μ
      · obtain ⟨sl, hs, hle⟩ := hop
        refine Or.inr ?_
        rw [hd.opv K hK i ⟨μ, Nat.lt_of_lt_of_le hμ (Nat.sub_le _ _)⟩ sl hs hle]
        rcases hz with hz | hz
        · exact hz
        · exact (hz ⟨sl, (hd.sel K).symm.trans hs, hle⟩).elim
      · exact Or.inl hop
  · refine ⟨(.inr (idx, κ, t), 0, z), rfl, ⟨o, ?_, ?_⟩, fun x hx ↦ ?_⟩
    · rw [hd.par]
      rwa [publicSeed_digTable] at ho
    · rw [cpre_pub_forsValue hd.pub]
      exact hdo
    · obtain ⟨rfl, hO⟩ := hfl1 _ _ hx
      rcases hz with hz | hz
      · rwa [cpre_forsSecret] at hz
      · exact (hz hO).elim

/-- **A witness of the reduction's condition wins CPRE** on the reduction's transcript. -/
theorem cpre_good_judge (hd : CpreDataOk h P s r d0) {p : CpreSt × QueryLog CpreS}
    (hI : CpreInv h P s r d0 w1 p) (hw1 : ∀ e ∈ w1, CpreQ1 (keySelect h (cpreT h P s r)) e.1)
    {H : HashInput → Option HashOutput} (hH : ∀ x o, H x = some o → o = h x)
    {w : CpreJ × ℕ × Digest} (hg : cpreGood d0 p.1.2.2 H w) : cpreJudgeP h P s p.2 w := by
  obtain ⟨-, ⟨w2, hlog, hw2⟩, hfl1, hfl2⟩ := hI
  have hw2' : ∀ e ∈ w2, ∃ j : CpreFJ, e.1 = .value (.inr j) 0 :=
    fun e he ↦ (hw2 e he).imp fun _ hj ↦ hj.1
  rw [hlog]
  obtain ⟨j, μ, z⟩ := w
  rcases j with ⟨K, i⟩ | ⟨idx, κ, t⟩
  · obtain ⟨hK, hμ, hwalk, hz⟩ := hg
    have hw' : walkH h P K i μ (chainLength - 1 - μ) z =
        (cpreT h P s r).endpoints K.1 K.2.1 K.2.2 i := by
      have e := Extract.chainWalk_sound hH hwalk
      rw [hd.par, cpre_pub_endpoints hd.pub] at e
      exact e
    refine ⟨cpre_valid P hw1 hw2', hμ, ?_, ?_⟩
    · show walkFwd (cpreG h P (.inl (K, i))) μ (chainLength - 1 - μ) z =
        walkFwd (cpreG h P (.inl (K, i))) 0 (chainLength - 1) (s (.inl (K, i)))
      rw [cpre_walkFwd_wots h P K i (by omega), hw',
        cpre_walk_chainValue h P s r hK i _ le_rfl]
      rfl
    · show z ≠ walkFwd (cpreG h P (.inl (K, i))) 0 μ (s (.inl (K, i))) ∨
        ¬Props.OpenedAtOrBelow (w1 ++ ⟨.reveal, P⟩ :: w2) (.inl (K, i)) μ
      rw [cpre_walk_chainValue h P s r hK i μ (by omega)]
      by_cases hop : ∃ sl, d0.sel K = some sl ∧ (sl.2 i).val ≤ μ
      · obtain ⟨sl, hs, hle⟩ := hop
        rcases hz with hz | hz
        · exact (hz ⟨sl, hs, hle⟩).elim
        · rw [hd.opv K hK i _ sl hs hle] at hz
          exact Or.inl hz
      · refine Or.inr fun hO ↦ hop ?_
        obtain ⟨sl, hs, hle⟩ := cpre_opened_inl P hw1 hw2' hμ hO
        exact ⟨sl, (hd.sel K).trans hs, hle⟩
  · obtain ⟨rfl, ⟨o, ho, hdo⟩, hfl⟩ := hg
    refine ⟨cpre_valid P hw1 hw2', Nat.one_pos, ?_, ?_⟩
    · show cpreG h P (.inr (idx, κ, t)) 0 z = cpreG h P (.inr (idx, κ, t)) 0 (s (.inr (idx, κ, t)))
      rw [cpreG_inr, cpreG_inr, ← cpre_dig_forsLeaf h P s r, ← cpre_forsValue_zero,
        ← cpre_pub_forsValue hd.pub, ← hdo, hH _ _ ho, hd.par]
      rfl
    · show z ≠ s (.inr (idx, κ, t)) ∨
        ¬Props.OpenedAtOrBelow (w1 ++ ⟨.reveal, P⟩ :: w2) (.inr (idx, κ, t)) 0
      by_cases hO : Props.OpenedAtOrBelow (w1 ++ ⟨.reveal, P⟩ :: w2) (.inr (idx, κ, t)) 0
      · obtain ⟨e, he, hej⟩ := cpre_opened_inr P hw1 hw2' hO
        obtain ⟨j', hj', hopen⟩ := hw2 e he
        rw [hej] at hj'
        cases hj'
        exact Or.inl (hfl _ (hfl2 _ hopen))
      · exact Or.inr hO

/-- **On the CPRE event of the forgery's trace, the judge accepts** the reduction's output. -/
theorem cpre_judge_of_event (hd : CpreDataOk h P s r d0)
    (hw1 : ∀ e ∈ w1, CpreQ1 (keySelect h (cpreT h P s r)) e.1) {p : CpreSt × QueryLog CpreS}
    (hI : CpreInv h P s r d0 w1 p) (forg : Forgery)
    (hev : EvCpreT h (cpreT h P s r) (forgTrace h (cpreT h P s r) forg) (logMsgs p.1.2.1)) :
    cpreJudgeP h P s p.2
      (cpreOut d0 p.1.2.2 (Extract.traceH h d0.pk forg.message forg.signature)) := by
  rw [cpre_pk_eq hd]
  obtain ⟨w, hw⟩ := cpre_exists_good hd hI hev
  exact cpre_good_judge hd hI hw1 Extract.traceH_sound (Classical.epsilon_spec ⟨w, hw⟩)

end Judge

/-! ## The reduction at a fixed table -/

section Run

variable (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (s : CpreJ → Digest)
  (r : Message → Digest)

theorem simulateQ_cpreAns_reveal :
    simulateQ (W.eager tab) (cpreAns W P s .reveal) = pure P :=
  simulateQ_pure _ _

/-- The FORS openings of a signature at the table. -/
theorem cpreDet_forsQ (Qq : CpreQ → Prop) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (hq : ∀ κ, Qq (.value (.inr (idx, κ, lv κ)) 0)) :
    CpreDet tab (cpreAns W P s) Qq (cpreForsQ W idx lv) fun fs ↦
      ∀ κ, fs κ = s (.inr (idx, κ, lv κ)) :=
  (cpreDet_tab _ 0 _ (fun κ v ↦ v = s (.inr (idx, κ, lv κ))) fun κ _ ↦
    cpreDet_valQ _ _ (simulateQ_cpreAns_value W tab P s _ _) (hq κ) rfl).mono
    (fun _ hfs κ ↦ hfs κ (List.mem_finRange κ)) fun _ h ↦ h

/-- **The reduction's signer at the table**: the table's signature, logged, and the FORS secrets
of the disclosed leaves recorded. -/
theorem cpreDet_handler {d0 : CpreData} (hd : CpreDataOk (W.hashOf tab) P s r d0) (sl : SignLog)
    (fl : List (CpreFJ × Digest)) (M : Message) :
    CpreDet tab (cpreAns W P s) (CpreQ2 (W.hashOf tab) (cpreT (W.hashOf tab) P s r) M)
      (cpreHandler W (d0, sl, fl) M) fun x ↦
        x.1 = (cpreT (W.hashOf tab) P s r).signature (cellHash (W.hashOf tab)) M ∧ x.2.1 = d0 ∧
        x.2.2.1 = sl ++ [⟨M, (cpreT (W.hashOf tab) P s r).signature (cellHash (W.hashOf tab)) M⟩] ∧
        ∀ j y, (j, y) ∈ x.2.2.2 ↔ (j, y) ∈ fl ∨ (y = s (.inr j) ∧
          ((cpreT (W.hashOf tab) P s r).signature (cellHash (W.hashOf tab)) M).isSome = true ∧
          (cpreT (W.hashOf tab) P s r).index M = j.1 ∧
          (cpreT (W.hashOf tab) P s r).leaves M j.2.1 = j.2.2) := by
  unfold cpreHandler
  refine cpreDet_bind (cpreDet_hash _ (Px := (· = W.hashOf tab _)) rfl) fun o0 ho0 ↦
    cpreDet_bind (cpreDet_hash _ (Px := (· = W.hashOf tab _)) rfl) fun o1 ho1 ↦ ?_
  subst ho0 ho1
  dsimp only
  rw [cpre_md_eq hd M]
  have hsig := cpre_signature_eq hd M
  show CpreDet _ _ _ (cpreSignIdx W d0 sl fl M ((cpreT (W.hashOf tab) P s r).index M)
    ((cpreT (W.hashOf tab) P s r).leaves M)) _
  unfold cpreSignIdx
  cases hL : cpreLayers d0 ((cpreT (W.hashOf tab) P s r).index M) with
  | none =>
    rw [hL, Option.map_none] at hsig
    refine cpreDet_pure ⟨hsig.symm, rfl, by rw [hsig], fun j y ↦ ⟨Or.inl, fun hj ↦ ?_⟩⟩
    rcases hj with hj | hj
    · exact hj
    · rw [hsig] at hj
      exact absurd hj.2.1 (by simp)
  | some lay =>
    rw [hL, Option.map_some] at hsig
    refine cpreDet_bind (cpreDet_forsQ W tab P s _ _ _ fun κ ↦
      ⟨_, rfl, by rw [hsig]; rfl, rfl, rfl⟩) fun fs hfs ↦ cpreDet_pure ⟨?_, rfl, ?_, ?_⟩
    · rw [hsig, cpre_sigOf_eq hd _ _ _ _ _ hfs]
    · rw [hsig, cpre_sigOf_eq hd _ _ _ _ _ hfs]
    · intro j y
      rw [List.mem_append, List.mem_map]
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨κ, -, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨hfs κ, by rw [hsig]; rfl, rfl, rfl⟩
      · rintro ⟨rfl, -, h1, h2⟩
        obtain ⟨j1, j2, j3⟩ := j
        dsimp only at h1 h2
        subst h1 h2
        exact ⟨j2, List.mem_finRange _, by rw [hfs]⟩

/-- **The reduction's kernel is the table's signer** through the state projection. -/
theorem cpre_hK {d0 : CpreData} {w1 : QueryLog CpreS} (hd : CpreDataOk (W.hashOf tab) P s r d0)
    (p : CpreSt × QueryLog CpreS) (hp : CpreInv (W.hashOf tab) P s r d0 w1 p) (M : Message) :
    Prod.map id (fun p : CpreSt × QueryLog CpreS ↦ p.1.2.1) <$>
        hKernel tab (cpreAns W P s) (cpreHandler W) p M =
      detKernel (W.hashOf tab) (cpreT (W.hashOf tab) P s r) p.1.2.1 M := by
  obtain ⟨⟨d, sl, fl⟩, log⟩ := p
  obtain ⟨hd0, -⟩ := hp
  dsimp only at hd0
  subst hd0
  obtain ⟨x, w, hrun, ⟨h1, -, h3, -⟩, -⟩ := cpreDet_handler W tab P s r hd sl fl M log
  simp only [hKernel, hrun, map_pure, Prod.map_apply, id_eq, detKernel, h1, h3]

/-- **The invariant is kept** by the reduction's kernel. -/
theorem cpreInv_step {d0 : CpreData} {w1 : QueryLog CpreS}
    (hd : CpreDataOk (W.hashOf tab) P s r d0) (p : CpreSt × QueryLog CpreS)
    (hp : CpreInv (W.hashOf tab) P s r d0 w1 p) (M : Message) :
    ∀ q ∈ support (hKernel tab (cpreAns W P s) (cpreHandler W) p M),
      CpreInv (W.hashOf tab) P s r d0 w1 q.2 := by
  obtain ⟨⟨d, sl, fl⟩, log⟩ := p
  obtain ⟨hd0, ⟨w2, hlog, hw2⟩, hfl1, hfl2⟩ := hp
  dsimp only at hd0 hlog hw2 hfl1 hfl2
  subst hd0
  obtain ⟨x, w, hrun, ⟨h1, h2, h3, h4⟩, hw⟩ := cpreDet_handler W tab P s r hd sl fl M log
  intro q hq
  simp only [hKernel, hrun, map_pure, support_pure, Set.mem_singleton_iff] at hq
  subst hq
  have hmsgs : logMsgs x.2.2.1 = logMsgs sl ++ [M] := by rw [h3, cpre_logMsgs_append]
  have hnew : ∀ j : CpreFJ, ForsOpened (W.hashOf tab) (cpreT (W.hashOf tab) P s r)
      (logMsgs x.2.2.1) j.1 j.2.1 j.2.2 ↔
        ForsOpened (W.hashOf tab) (cpreT (W.hashOf tab) P s r) (logMsgs sl) j.1 j.2.1 j.2.2 ∨
          (((cpreT (W.hashOf tab) P s r).signature (cellHash (W.hashOf tab)) M).isSome = true ∧
            (cpreT (W.hashOf tab) P s r).index M = j.1 ∧
            (cpreT (W.hashOf tab) P s r).leaves M j.2.1 = j.2.2) := by
    intro j
    rw [hmsgs]
    constructor
    · rintro ⟨M', hM', hs⟩
      rcases List.mem_append.mp hM' with hM' | hM'
      · exact Or.inl ⟨M', hM', hs⟩
      · rw [List.mem_singleton.mp hM'] at hs
        exact Or.inr hs
    · rintro (ho | hs)
      · exact cpre_forsOpened_append _ ho
      · exact ⟨M, List.mem_append_right _ (List.mem_singleton_self M), hs⟩
  refine ⟨h2, ⟨w2 ++ w, by dsimp only; rw [hlog]; simp, fun e he ↦ ?_⟩, fun j y hy ↦ ?_,
    fun j hj ↦ ?_⟩
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨j, hj, ho⟩ := hw2 e he
      exact ⟨j, hj, (hnew j).2 (Or.inl ho)⟩
    · obtain ⟨j, hj, hs⟩ := hw e he
      exact ⟨j, hj, (hnew j).2 (Or.inr hs)⟩
  · rcases (h4 j y).1 hy with hy | ⟨rfl, hs⟩
    · obtain ⟨rfl, ho⟩ := hfl1 j y hy
      exact ⟨rfl, (hnew j).2 (Or.inl ho)⟩
    · exact ⟨rfl, (hnew j).2 (Or.inr hs)⟩
  · rcases (hnew j).1 hj with ho | hs
    · exact (h4 j _).2 (Or.inl (hfl2 j ho))
    · exact (h4 j _).2 (Or.inr ⟨rfl, hs⟩)

theorem cpre_logImpl_hash (ans : (q : CpreQ) → OracleComp W.Oracles (CpreS.Range q))
    (l : HashInput) :
    simulateQ (logImpl tab ans) (cpreHash W l) =
      (pure (W.hashOf tab l) : StateT (QueryLog CpreS) ProbComp HashOutput) := by
  refine StateT.ext fun log ↦ ?_
  rw [cpreHash, run_simulateQ_logImpl_liftW, W.simulateQ_hash, map_pure, StateT.run_pure]

theorem cpre_logImpl_mapM (ans : (q : CpreQ) → OracleComp W.Oracles (CpreS.Range q)) :
    ∀ xs : List HashInput, simulateQ (logImpl tab ans) (xs.mapM (cpreHash W)) =
      (pure (xs.map (W.hashOf tab)) : StateT (QueryLog CpreS) ProbComp (List HashOutput))
  | [] => by rw [List.mapM_nil, simulateQ_pure]; rfl
  | x :: xs => by
    simp only [List.mapM_cons, simulateQ_bind, cpre_logImpl_hash W tab ans, pure_bind,
      cpre_logImpl_mapM ans xs, simulateQ_pure, List.map_cons]

omit W tab in
theorem cpreLookup_map (f : HashInput → HashOutput) :
    ∀ xs : List HashInput, cpreLookup xs (xs.map f) = traceOf xs f
  | [] => by
    funext y
    simp [cpreLookup, traceOf]
  | x :: xs => by
    funext y
    have ih := congrFun (cpreLookup_map f xs) y
    simp only [List.map_cons, cpreLookup, ih, traceOf]
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy]

/-- **The reduction's output at the table**: the witness of the forgery's verification trace. -/
theorem cpre_post_run (ans : (q : CpreQ) → OracleComp W.Oracles (CpreS.Range q)) (a : CpreData)
    (forg : Forgery) (st : CpreSt) (log : QueryLog CpreS) :
    (simulateQ (logImpl tab ans) (cprePost W a forg st)).run log =
      pure (cpreOut a st.2.2 (Extract.traceH (W.hashOf tab) a.pk forg.message forg.signature),
        log) := by
  have e : simulateQ (logImpl tab ans) (cprePost W a forg st) =
      (pure (cpreOut a st.2.2 (Extract.traceH (W.hashOf tab) a.pk forg.message
        forg.signature)) : StateT (QueryLog CpreS) ProbComp _) := by
    simp only [cprePost, simulateQ_bind, simulateQ_recVerify (logImpl tab ans) (cpreHash W)
      (W.hashOf tab) (cpre_logImpl_hash W tab ans), pure_bind, cpre_logImpl_mapM W tab ans,
      simulateQ_pure, cpreLookup_map, traceOf_eq]
  rw [e, StateT.run_pure]

/-- The CPRE judge at the table. -/
theorem cpre_judge_sim (log : QueryLog CpreS) (out : CpreJ × ℕ × Digest) :
    simulateQ (W.eager tab) ((Props.cpre W cpreChains slotColl).judge (P, s) log out) =
      pure (Props.holds (cpreJudgeP (W.hashOf tab) P s log out)) := by
  simp only [Props.cpre, simulateQ_bind, simulateQ_walk, pure_bind, simulateQ_pure]
  rfl

/-- After the setup, the reduction's game is a decision on the canonical run. -/
theorem cpre_probAt_round (A : SAdv W) (d0 : CpreData) (w : QueryLog CpreS) :
    W.probAt tab (QuantumComp₂.bind (QuantumComp₂.bind
        (kRunL W (hKernel tab (cpreAns W P s) (cpreHandler W)) (A d0.pk) (d0, [], []) w) fun x ↦
          ((simulateQ (logImpl tab (cpreAns W P s)) (cprePost W d0 x.1.1 x.1.2)).run
            x.2).toQuantumAt (QComp.coinImpl W.spec _)) fun x ↦
          (simulateQ (W.eager tab) ((Props.cpre W cpreChains slotColl).judge (P, s) x.2
            x.1)).toQuantumAt (QComp.coinImpl W.spec _)) =
      W.probAt tab ((kRunQ W (hKernel tab (cpreAns W P s) (cpreHandler W)) (A d0.pk)
        ((d0, [], []), w)).map (cpreDRed (W.hashOf tab) P s d0)) := by
  refine probAt_eq_of_run₂ W tab ?_
  rw [QuantumComp₂.bind_assoc, kRunL_eq_map,
    QuantumComp₂.map_eq_bind_pure (cpreDRed (W.hashOf tab) P s d0),
    QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]
  refine run₂_bind_congr rfl fun a ↦ ?_
  rw [cpre_post_run]
  refine (run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _) _).trans ?_
  rw [cpre_judge_sim]
  exact run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _) (classicalOn_pure _)

/-- **One randomizer function**: the game at the table read through the CPRE decision is at most
the reduction's game decision. -/
theorem cpre_round_ge (A : SAdv W) (d0 : CpreData) (w1 : QueryLog CpreS)
    (hd : CpreDataOk (W.hashOf tab) P s r d0)
    (hw1 : ∀ e ∈ w1, CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) e.1) :
    gameAt W tab A (cpreT (W.hashOf tab) P s r)
        (cpreDec (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) ≤
      W.probAt tab ((kRunQ W (hKernel tab (cpreAns W P s) (cpreHandler W)) (A d0.pk)
        ((d0, [], []), w1 ++ [⟨.reveal, P⟩])).map (cpreDRed (W.hashOf tab) P s d0)) := by
  let d₂ : Forgery × (CpreSt × QueryLog CpreS) → Bool := fun x ↦
    Props.holds (CpreInv (W.hashOf tab) P s r d0 w1 x.2) &&
      cpreDec (W.hashOf tab) (cpreT (W.hashOf tab) P s r) (x.1, x.2.1.2.1)
  have hsim := run₂_map_kRunQ_sim (W.runtime tab)
    (detKernel (W.hashOf tab) (cpreT (W.hashOf tab) P s r))
    (hKernel tab (cpreAns W P s) (cpreHandler W)) (CpreInv (W.hashOf tab) P s r d0 w1)
    (fun p ↦ p.1.2.1) (fun p hp M ↦ cpre_hK W tab P s r hd p hp M)
    (fun p hp M ↦ cpreInv_step W tab P s r hd p hp M) (A d0.pk)
    ((d0, [], []), w1 ++ [⟨.reveal, P⟩]) (cpreInv_init _ P s r d0 w1)
    (cpreDec (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) d₂ fun a st hst ↦ by
      simp only [d₂, Props.holds_eq_true.mpr hst, Bool.true_and]
  have h1 : gameAt W tab A (cpreT (W.hashOf tab) P s r)
      (cpreDec (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) =
      W.probAt tab ((kRunQ W (hKernel tab (cpreAns W P s) (cpreHandler W)) (A d0.pk)
        ((d0, [], []), w1 ++ [⟨.reveal, P⟩])).map d₂) := by
    unfold gameAt
    rw [← cpre_pk_eq hd]
    exact (probAt_eq_of_run₂ W tab hsim).symm
  rw [h1]
  have hle := probAt_map_le_sum W tab (kRunQ W (hKernel tab (cpreAns W P s) (cpreHandler W))
    (A d0.pk) ((d0, [], []), w1 ++ [⟨.reveal, P⟩])) d₂ {()}
    (fun _ ↦ cpreDRed (W.hashOf tab) P s d0) fun x hx ↦ ⟨(), Finset.mem_singleton_self _, ?_⟩
  · simpa using hle
  simp only [d₂, Bool.and_eq_true, Props.holds_eq_true] at hx
  obtain ⟨hI, hc⟩ := hx
  exact Props.holds_eq_true.mpr
    (cpre_judge_of_event hd hw1 hI x.1 (Props.holds_eq_true.mp hc))

/-- **The reduction's setup at the table**: uniform randomizers, the setup's data and
transcript, then the reveal. -/
theorem cpre_run_pre (hW : W.CoinsFair) :
    ∃ (D : (Message → Digest) → CpreData) (w : (Message → Digest) → QueryLog CpreS),
      (simulateQ (logImpl tab (cpreAns W P s)) (cprePre W)).run [] =
        ($ᵗ (Message → Digest)) >>= (fun r ↦ pure (D r, w r ++ [⟨.reveal, P⟩])) ∧
      ∀ r, CpreDataOk (W.hashOf tab) P s r (D r) ∧
        ∀ e ∈ w r, CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) e.1 := by
  obtain ⟨x0, w0, hrun0, -, -⟩ := cpreDet_stage W tab P s (fun _ ↦ 0) []
  have hst : ∀ r, ((∀ p : Pos, KeyPart p.1 → CpreP p.1 →
      x0.1 p.1 = (cpreT (W.hashOf tab) P s r).dig p.1) ∧
      (∀ K, x0.2.1 K = keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r) K) ∧
      ∀ K i (μ : Fin chainLength) sl, x0.2.1 K = some sl → sl.2 i ≤ μ →
        x0.2.2 (K, i, μ) = walkFwd (cpreG (W.hashOf tab) P (.inl (K, i))) 0 μ.val
          (s (.inl (K, i)))) ∧
      ∀ e ∈ w0, CpreQ1 (keySelect (W.hashOf tab) (cpreT (W.hashOf tab) P s r)) e.1 := by
    intro r
    obtain ⟨x, w, hrun, hx, hw⟩ := cpreDet_stage W tab P s r []
    have e := (OracleComp.pure_inj _ _).1 (hrun.symm.trans hrun0)
    simp only [List.nil_append, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hx, hw⟩
  have hrev : ∀ log : QueryLog CpreS,
      (simulateQ (logImpl tab (cpreAns W P s)) (cpreRevQ W)).run log =
        pure (P, log ++ [⟨.reveal, P⟩]) :=
    cpre_run_portQ .reveal (simulateQ_cpreAns_reveal W tab P s)
  refine ⟨fun r ↦ ⟨r, x0.1, x0.2.1, x0.2.2, P⟩, fun _ ↦ w0, ?_, fun r ↦
    ⟨⟨rfl, rfl, cpre_dig_ofDig (hst r).1.1, (hst r).1.2.1, fun K hK i μ sl hs hle ↦
      ((hst r).1.2.2 K i μ sl hs hle).trans
        (cpre_walk_chainValue _ P s r hK i _ (by have := μ.isLt; omega))⟩, (hst r).2⟩⟩
  simp only [cprePre, simulateQ_bind, StateT.run_bind, run_simulateQ_logImpl_liftW,
    W.simulateQ_sample hW tab, bind_map_left, hrun0, pure_bind, hrev, simulateQ_pure,
    StateT.run_pure, List.nil_append]

theorem cpre_unifAvg_mono {X : Type} [Fintype X] {F G : X → ℝ≥0∞} (hFG : ∀ x, F x ≤ G x) :
    unifAvg X F ≤ unifAvg X G :=
  mul_le_mul' le_rfl (Finset.sum_le_sum fun x _ ↦ hFG x)

/-- **At the challenger's `PK.seed` and chain starts**, the randomizer average of the game read
through the CPRE decision is at most the reduction's game. -/
theorem cpre_ps_ge (A : SAdv W) (hW : W.CoinsFair) :
    unifAvg (Message → Digest) (fun r ↦ gameAt W tab A (cpreT (W.hashOf tab) P s r)
        (cpreDec (W.hashOf tab) (cpreT (W.hashOf tab) P s r))) ≤
      W.probAt tab (QuantumComp₂.bind (slNormal tab (cpreAns W P s) (cprePre W)
        (fun a ↦ A a.pk) (fun a ↦ (a, [], [])) (cpreHandler W) (cprePost W)) fun x ↦
          (simulateQ (W.eager tab) ((Props.cpre W cpreChains slotColl).judge (P, s) x.2
            x.1)).toQuantumAt (QComp.coinImpl W.spec _)) := by
  obtain ⟨D, w, hrun, hD⟩ := cpre_run_pre W tab P s hW
  unfold slNormal
  rw [QuantumComp₂.bind_assoc,
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _), hrun,
    tsum_prEvent_bind_mul]
  simp only [tsum_prEvent_pure_mul]
  rw [tsum_prEvent_uniformSample]
  refine cpre_unifAvg_mono fun r ↦ ?_
  exact (cpre_round_ge W tab P s r A (D r) (w r) (hD r).1 (hD r).2).trans_eq
    (cpre_probAt_round W tab P s A (D r) _).symm

/-- The law of the CPRE challenger's setup: uniform `PK.seed` and chain starts. -/
theorem cpre_tsum_setup (hW : W.CoinsFair) (f : PublicParameter × (CpreJ → Digest) → ℝ≥0∞) :
    ∑' a, Pr{let z ← simulateQ (W.eager tab) (Props.cpre W cpreChains slotColl).setup}[z = a] *
        f a =
      unifAvg PublicParameter fun P ↦ unifAvg (CpreJ → Digest) fun s ↦ f (P, s) := by
  simp only [Props.cpre, simulateQ_bind, W.simulateQ_sample hW tab, simulateQ_pure,
    tsum_prEvent_bind_mul, tsum_prEvent_pure_mul, tsum_prEvent_uniformSample]

end Run

/-! ## The CPRE hop -/

section Hop

variable (W : OracleWorld) (tab : W.Tab) (A : SAdv W)

/-- **The CPRE hop of Theorem 2**: at every table of a world with fair coins, the ideal game read
through the CPRE decision is at most the CPRE success of the reduction `cpreRed W A`. -/
theorem ideal_cpre_le (hW : W.CoinsFair) :
    ideal W tab A (cpreDec (W.hashOf tab)) ≤
      Props.cpreSucc W cpreChains slotColl tab (cpreRed W A) := by
  have hsucc : Props.cpreSucc W cpreChains slotColl tab (cpreRed W A) =
      unifAvg PublicParameter fun P ↦ unifAvg (CpreJ → Digest) fun s ↦
        W.probAt tab (QuantumComp₂.bind (slNormal tab (cpreAns W P s) (cprePre W)
          (fun a ↦ A a.pk) (fun a ↦ (a, [], [])) (cpreHandler W) (cprePost W)) fun x ↦
            (simulateQ (W.eager tab) ((Props.cpre W cpreChains slotColl).judge (P, s) x.2
              x.1)).toQuantumAt (QComp.coinImpl W.spec _)) :=
    (probAt_eq_of_run₂ W tab (run₂_game_slRed tab (Props.cpre W cpreChains slotColl)
      (fun _ ↦ cprePre W) (fun _ a ↦ A a.pk) (fun _ a ↦ (a, [], [])) (fun _ ↦ cpreHandler W)
      (fun _ ↦ cprePost W))).trans ((probAt_bind_classicalOn W tab
        (classicalOn_coinImpl_toQuantumAt _ _) _).trans (cpre_tsum_setup W tab hW _))
  rw [hsucc]
  unfold ideal
  refine cpre_unifAvg_mono fun P ↦ ?_
  rw [← cpreJ_law]
  exact cpre_unifAvg_mono fun s ↦ cpre_ps_ge W tab P s A hW

/-- **The reduction's charges**: `A`'s hash calls plus the honest work (`c₀` in the setup, `k`
per signing request, `c₁` in the output), and its CPRE queries (`q₀` in the setup, `kq` per
signing request, `q₁` in the output). -/
theorem isChargeBound_cpreRed {c₀ c₁ k q₀ q₁ kq n m : ℕ}
    (hpre : Common.QueryCostAtMost (cprePre W) (hcallCost W (R' := CpreS)) c₀)
    (hσ : ∀ st M, Common.QueryCostAtMost (cpreHandler W st M) (hcallCost W (R' := CpreS)) k)
    (hpost : ∀ a f st,
      Common.QueryCostAtMost (cprePost W a f st) (hcallCost W (R' := CpreS)) c₁)
    (qpre : Common.QueryCostAtMost (cprePre W) (portCost W (R' := CpreS)) q₀)
    (qσ : ∀ st M, Common.QueryCostAtMost (cpreHandler W st M) (portCost W (R' := CpreS)) kq)
    (qpost : ∀ a f st,
      Common.QueryCostAtMost (cprePost W a f st) (portCost W (R' := CpreS)) q₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (cpreRed W A u) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) ∧
      IFreeM.IsChargeBound (cpreRed W A u) (cmdCharge callCharge) (q₀ + (kq * m + q₁)) :=
  ⟨isChargeBound_slRed_hash W _ _ _ _ _ hpre hσ hpost (fun a ↦ hn a.pk) fun a ↦ hm a.pk,
    isChargeBound_slRed_call W _ _ _ _ _ qpre qσ qpost fun a ↦ hm a.pk⟩

end Hop

end Quantum.StdModel.Sphincs

end
