module

public import FORS.GraphView.HonestGame
public import FORS.LazyRun.HonestReadFrom

@[expose] public section

section

/-! The honest signer's reads are harmless from a prepared state (`honestOkFrom_signCostSourceH`):
its message-digest calls read message-digest inputs, and its WOTS+C counter searches read only
trials the initial cache answers, stopping where the cache's answers stop them (`SearchCached`).
The trials past a search's first success are neither prepared nor untargeted, so the signer is
not `HonestOk`; no run from a prepared state reaches them, which `HonestOkFrom` accounts for. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph HiddenDebt HiddenCost
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] encodingAttemptLimit digestAttemptLimit

/-! ### Reads of a hash computation from a prepared state -/

/-- Every query of a hash computation a run from `initial` can reach satisfies `good`: at a cached
input only the cached answer's continuation counts. -/
def ReadsFrom (good : HashInput → Prop) (initial : QueryCache HashSpec) {α : Type}
    (computation : OracleComp HashSpec α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next =>
      good input ∧ ∀ value : HashOutput, (∀ output, initial input = some output → value = output) → next value)
    computation

theorem readsFrom_pure (good : HashInput → Prop) (initial : QueryCache HashSpec) {α : Type} (value : α) :
    ReadsFrom good initial (pure value : OracleComp HashSpec α) := trivial

theorem readsFrom_query_bind (good : HashInput → Prop) (initial : QueryCache HashSpec) {α : Type}
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    ReadsFrom good initial (liftM (HashSpec.query input) >>= next) ↔
      good input ∧ ∀ value, (∀ output, initial input = some output → value = output) →
        ReadsFrom good initial (next value) :=
  Iff.rfl

theorem readsFrom_bind (good : HashInput → Prop) (initial : QueryCache HashSpec) {α β : Type}
    {first : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (hfirst : ReadsFrom good initial first) (hnext : ∀ value, ReadsFrom good initial (next value)) :
    ReadsFrom good initial (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc]
      obtain ⟨hin, hrest⟩ := (readsFrom_query_bind good initial input rest).1 hfirst
      exact (readsFrom_query_bind good initial input _).2 ⟨hin, fun value hv => ih value (hrest value hv)⟩

theorem readsFrom_sequenceFin (good : HashInput → Prop) (initial : QueryCache HashSpec) {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp HashSpec α),
      (∀ i, ReadsFrom good initial (computation i)) → ReadsFrom good initial (sequenceFin computation)
  | 0, _, _ => readsFrom_pure good initial _
  | n + 1, computation, h => by
      unfold sequenceFin
      exact readsFrom_bind good initial (h 0) fun _ =>
        readsFrom_bind good initial (readsFrom_sequenceFin good initial (fun i : Fin n => computation i.succ)
          fun i => h i.succ) fun _ => readsFrom_pure good initial _

/-- An oracle hash of a good input, then a continuation constrained at the allowed answers. -/
theorem readsFrom_oracleHash_bind (good : HashInput → Prop) (initial : QueryCache HashSpec) {α : Type}
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) (hgood : good input)
    (hnext : ∀ value, (∀ output, initial input = some output → value = output) →
      ReadsFrom good initial (next value)) :
    ReadsFrom good initial ((oracleHash input : OracleComp HashSpec HashOutput) >>= next) :=
  (readsFrom_query_bind good initial input next).2 ⟨hgood, hnext⟩

variable (tg : HiddenDebt.Targeting HashInput HashOutput Coordinate) (initial : QueryCache HashSpec)
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **A hash computation run through honest reads** is `HonestOkFrom` when every input it can
reach from `initial` is harmless. -/
theorem honestOkFrom_liftHonest {α : Type} (computation : OracleComp HashSpec α)
    (h : ReadsFrom (HonestGood tg initial model) initial computation) :
    HonestOkFrom tg initial model (liftHonest computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestOkFrom_pure tg initial model value
  | query_bind input next ih =>
      obtain ⟨hin, hrest⟩ := (readsFrom_query_bind _ initial input next).1 h
      have hlift : liftHonest (liftM (HashSpec.query input) >>= next) =
          HiddenCost.honestRead (D := HashInput) (R := HashOutput) (ι := Coordinate) input >>=
            fun value => liftHonest (next value) := by
        simp only [liftHonest, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, honestHash]
      rw [hlift]
      exact honestOkFrom_honestRead_bind tg initial model input _ hin fun value hv => ih value (hrest value hv)

/-! ### The signer's reads -/

/-- A message-digest call reads one message-digest input. -/
theorem readsFrom_messageDigestCall (good : HashInput → Prop)
    (hmsg : ∀ parameter root message randomness call, good (messageDigestInput parameter root message randomness call))
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness)
    (call : DigestCall) :
    ReadsFrom good initial (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) := by
  rw [messageDigestCall, ← bind_pure (oracleHash _)]
  exact readsFrom_oracleHash_bind good initial _ _ (hmsg _ _ _ _ _) fun _ _ => readsFrom_pure good initial _

theorem readsFrom_messageDigest (good : HashInput → Prop)
    (hmsg : ∀ parameter root message randomness call, good (messageDigestInput parameter root message randomness call))
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    ReadsFrom good initial (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) := by
  rw [messageDigest]
  exact readsFrom_bind good initial (readsFrom_sequenceFin good initial _ fun call =>
    readsFrom_messageDigestCall initial good hmsg parameter root message randomness call)
    fun _ => readsFrom_pure good initial _

/-- The raw input of trial `start` of a key's WOTS+C counter search. -/
def trialInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (start : ℕ) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf) (message ++ bytesBE 4 (BitVec.ofNat counterBits start))

/-- The trials a key's counter search makes from `start`, answered by `cache`, are all cached:
each trial is, and the search goes on only past a trial whose cached answer encodes nothing. -/
def SearchCached (cache : QueryCache HashSpec) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) : ℕ → ℕ → Prop
  | 0, _ => True
  | attempts + 1, start => ∃ output, cache (trialInput parameter lay tree leaf message start) = some output ∧
      (TargetSum.decodeDigest (truncateHash output) = none →
        SearchCached cache parameter lay tree leaf message attempts (start + 1))

theorem searchCached_mono {cache cache' : QueryCache HashSpec}
    (hext : ∀ input output, cache input = some output → cache' input = some output)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) :
    ∀ attempts start, SearchCached cache parameter lay tree leaf message attempts start →
      SearchCached cache' parameter lay tree leaf message attempts start
  | 0, _, _ => trivial
  | attempts + 1, start, ⟨output, hout, hnext⟩ =>
      ⟨output, hext _ _ hout, fun hnone =>
        searchCached_mono hext parameter lay tree leaf message attempts (start + 1) (hnext hnone)⟩

/-- A counter search whose trials are cached reads only harmless inputs: cached and unparsed. -/
theorem readsFrom_search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput)
    (hparse : ∀ start, model.parse (trialInput parameter lay tree leaf message start) = none) :
    ∀ attempts start, SearchCached initial parameter lay tree leaf message attempts start →
      ReadsFrom (HonestGood tg initial model) initial
        (ReferenceChoice.search parameter lay tree leaf message attempts start)
  | 0, _, _ => by
      rw [ReferenceChoice.search]
      exact readsFrom_pure _ initial _
  | attempts + 1, start, ⟨output, hout, hnext⟩ => by
      rw [ReferenceChoice.search, encode, tweakableHash, bind_assoc, bind_assoc]
      refine readsFrom_oracleHash_bind _ initial _ _ ⟨hparse start, Or.inl ?_⟩ fun value hv => ?_
      · change initial (trialInput parameter lay tree leaf message start) ≠ none
        rw [hout]
        exact Option.some_ne_none _
      · rw [hv output hout, pure_bind, pure_bind]
        cases hdec : TargetSum.decodeDigest (truncateHash output) with
        | none =>
            exact readsFrom_search parameter lay tree leaf message hparse attempts (start + 1) (hnext hdec)
        | some encoding => exact readsFrom_pure _ initial _

/-! ### The honest signer -/

theorem honestOkFrom_liftCoins {α : Type} (computation : ProbComp α) :
    HonestOkFrom tg initial model (liftM computation : OracleComp CostSpecH α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestOkFrom_pure tg initial model value
  | query_bind draw rest ih =>
      rw [liftM_bind]
      exact (honestOkFrom_query_bind tg initial model (.inl (.inl draw)) _).2
        ⟨fun _ h => (by cases h), fun value _ => ih value⟩

theorem honestOkFrom_sequenceDep :
    ∀ {n : ℕ} {α : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpecH (Option (α i))),
      (∀ i, HonestOkFrom tg initial model (computation i)) →
        HonestOkFrom tg initial model (sequenceDep computation)
  | 0, _, _, _ => honestOkFrom_pure tg initial model _
  | n + 1, α, computation, h => by
      rw [sequenceDep]
      refine honestOkFrom_bind tg initial model (h (Fin.last n)) fun last => ?_
      cases last with
      | none => exact honestOkFrom_pure tg initial model _
      | some last =>
          refine honestOkFrom_bind tg initial model
            (honestOkFrom_sequenceDep (α := fun i => α i.castSucc) (fun i => computation i.castSucc)
              fun i => h i.castSucc) fun init => ?_
          cases init with
          | none => exact honestOkFrom_pure tg initial model _
          | some init => exact honestOkFrom_pure tg initial model _

/-- The harmless inputs the signer reads: message-digest inputs, and the cached, unparsed trials
of every key's counter search on its public message. -/
structure SignerReadsGood (parameter : PublicParameter) (data : PublicData) : Prop where
  digest : ∀ parameter' root message randomness call,
    HonestGood tg initial model (messageDigestInput parameter' root message randomness call)
  trialParse : ∀ lay tree leaf message start, model.parse (trialInput parameter lay tree leaf message start) = none
  searched : ∀ lay tree leaf, SearchCached initial parameter lay tree leaf (data.keyMessage lay tree leaf)
    encodingAttemptLimit 0

theorem honestOkFrom_finishCostSourceH (parameter : PublicParameter) (data : PublicData)
    (hgood : SignerReadsGood tg initial model parameter data) (message : Message) (randomness : Randomness) :
    HonestOkFrom tg initial model (finishCostSourceH parameter data message randomness) := by
  rw [finishCostSourceH]
  refine honestOkFrom_bind tg initial model (honestOkFrom_liftHonest tg initial model _
    (readsFrom_messageDigest initial _ hgood.digest parameter data.root message randomness)) fun digest => ?_
  refine honestOkFrom_bind tg initial model (honestOkFrom_sequenceDep tg initial model _ fun lay =>
    honestOkFrom_liftHonest tg initial model _ (readsFrom_search tg initial model parameter lay _ _ _
      (hgood.trialParse lay _ _ _) _ _ (hgood.searched lay _ _))) fun found => ?_
  cases found with
  | none => exact honestOkFrom_pure tg initial model _
  | some found =>
      refine honestOkFrom_bind tg initial model (honestOkFrom_sequenceFin tg initial model _ fun lay =>
        honestOkFrom_sequenceFin tg initial model _ fun chain => honestOkFrom_reveal tg initial model _)
        fun values => ?_
      refine honestOkFrom_bind tg initial model (honestOkFrom_sequenceFin tg initial model _ fun κ => ?_)
        fun _ => honestOkFrom_pure tg initial model _
      rw [treeCostSourceH]
      exact honestOkFrom_bind tg initial model (honestOkFrom_sequenceFin tg initial model _ fun _ =>
        honestOkFrom_reveal tg initial model _) fun _ => honestOkFrom_pure tg initial model _

theorem honestOkFrom_signCostSourceLoopH (parameter : PublicParameter) (data : PublicData)
    (hgood : SignerReadsGood tg initial model parameter data) (message : Message) (step : Randomness) :
    ∀ attempts randomness,
      HonestOkFrom tg initial model (signCostSourceLoopH parameter data message step attempts randomness)
  | 0, _ => by
      rw [signCostSourceLoopH]
      exact honestOkFrom_pure tg initial model _
  | attempts + 1, randomness => by
      rw [signCostSourceLoopH]
      refine honestOkFrom_bind tg initial model (honestOkFrom_liftHonest tg initial model _
        (readsFrom_messageDigestCall initial _ hgood.digest parameter data.root message randomness firstCall))
        fun first => ?_
      split
      · exact honestOkFrom_finishCostSourceH tg initial model parameter data hgood message randomness
      · exact honestOkFrom_signCostSourceLoopH parameter data hgood message step attempts (randomness + step)

/-- **The honest signer's reads are harmless from a prepared state.** -/
theorem honestOkFrom_signCostSourceH (parameter : PublicParameter) (data : PublicData)
    (hgood : SignerReadsGood tg initial model parameter data) (message : Message) :
    HonestOkFrom tg initial model (signCostSourceH parameter data message) := by
  rw [signCostSourceH]
  exact honestOkFrom_bind tg initial model (honestOkFrom_liftCoins tg initial model _) fun start =>
    honestOkFrom_signCostSourceLoopH tg initial model parameter data hgood message _ _ start

end FORS.Security.GraphView

end
