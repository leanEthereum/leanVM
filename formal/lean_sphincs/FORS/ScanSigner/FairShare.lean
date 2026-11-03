import FORS.ScanSigner.LazySigner

/-! The grinding signer's view of message-digest blocks, and its fair share. A pair is a message
with a randomizer, and its blocks are the inputs of the `digestCalls` digest calls (`pblk`). A trial
reads only the block that carries the index (`blk`, the `firstCall` block) and tests landing on it;
the rest of the pair follows in the final assembly, and only if it landed. The encoding search and
the reveals never query a message-digest input, so after those calls the selected pair's blocks are
what the signature discloses (`all_read_bound`, `finish_boundAll`). A cached landed pair of the
signed message is selected with probability at most `1 / (n + R)` when the message has `n` cached
landed pairs: every trial picks each of them with probability `2^-128` and a fresh landed pair with
probability at least `R · 2^-128`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsSigner

variable [Params]

open Concrete HiddenCost HiddenDebt GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A message-digest input, for any public parameter and payload. -/
def IsMsgInput (input : HashInput) : Prop :=
  ∃ parameter call payload, input = tweakableHashInput parameter (.message call) payload

/-- No query of a hash computation is a message-digest input. -/
def NoMsg {α : Type} (computation : OracleComp HashSpec α) : Prop :=
  computation.IsQueryBoundP IsMsgInput 0

theorem NoMsg.pure' {α : Type} (value : α) : NoMsg (pure value : OracleComp HashSpec α) := trivial

theorem NoMsg.bind {α β : Type} {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : NoMsg oa) (hnext : ∀ value, NoMsg (next value)) : NoMsg (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [NoMsg] using this

theorem NoMsg.query {input : HashInput} (h : ¬IsMsgInput input) :
    NoMsg (oracleHash input : OracleComp HashSpec HashOutput) := by
  simp only [NoMsg, oracleHash, HasQuery.query]
  rw [isQueryBoundP_query_iff]
  exact fun hm => absurd hm h

theorem not_msg_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : (hashDomainFields domain).tag ≠ 12) : ¬IsMsgInput (tweakableHashInput parameter domain payload) := by
  rintro ⟨parameter', call', payload', heq⟩
  have h := (tweakableInput_injective heq).1
  apply hdomain
  rw [h]
  rfl

theorem NoMsg.tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : (hashDomainFields domain).tag ≠ 12) :
    NoMsg (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  exact NoMsg.bind (NoMsg.query (not_msg_tweakable parameter domain payload hdomain)) fun _ => NoMsg.pure' _

theorem NoMsg.encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) :
    NoMsg (Concrete.encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact NoMsg.bind (NoMsg.tweakableHash _ _ _ (by simp [hashDomainFields, treeFields])) fun _ => NoMsg.pure' _

theorem NoMsg.search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) : ∀ attempts start,
    NoMsg (ReferenceChoice.search parameter lay tree leaf message attempts start)
  | 0, _ => NoMsg.pure' _
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine NoMsg.bind (NoMsg.encode _ _ _ _ _ _) fun found => ?_
      cases found with
      | none => exact NoMsg.search parameter lay tree leaf message attempts (start + 1)
      | some _ => exact NoMsg.pure' _

end FORS.Security.ForsSigner

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

omit [Fintype ι] [SampleableType R] in
/-- One ordinary read avoids every input but its own. -/
theorem avoids_read (avoid : D → Prop) (y : D) (h : ¬avoid y) :
    Avoids avoid (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl y)))) :
      OracleComp (SourceCostSpec D R ι) R) := by
  rw [← bind_pure (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl y)))) :
    OracleComp (SourceCostSpec D R ι) R)]
  exact (avoids_query_bind avoid _ _).2 ⟨fun _ hb => by cases hb; exact h, fun _ => avoids_pure _ _⟩

/-- A family whose head is known splits off that head. -/
theorem allSome_cons {n : Nat} {α : Type} (values : Fin (n + 1) → Option α) {head : α}
    (h0 : values 0 = some head) :
    Completeness.allSome (α := fun _ => α) values =
      (Completeness.allSome (α := fun _ => α) fun index : Fin n => values index.succ).map
        fun tail => Fin.cases head tail := by
  unfold Completeness.allSome
  by_cases hall : ∀ index : Fin n, (values index.succ).isSome
  · rw [dif_pos hall, dif_pos (fun index => Fin.cases (by rw [h0]; rfl) hall index),
      Option.map_some]
    refine congrArg some (funext fun index => ?_)
    induction index using Fin.cases with
    | zero => simp [h0]
    | succ index => rfl
  · rw [dif_neg hall, dif_neg fun h => hall fun index => h index.succ, Option.map_none]

omit [Fintype ι] in
/-- The value of an option read through a map. -/
theorem elim_map {α β : Type} (values : Option α) (step : α → β) (g : β → ℝ≥0∞) :
    ((values.map step).elim 0 g : ℝ≥0∞) = values.elim 0 fun value => g (step value) := by
  cases values <;> rfl

omit [Fintype ι] in
/-- **A family of cached entries, read in order and kept.** The reads leave the entries untouched,
so a final value that only reads them is its value at their cached answers. -/
theorem all_read_bound {β : Type} : ∀ {n : Nat} (x : Fin n → D), Function.Injective x →
    (∀ index, model.parse (x index) = none) → ∀ (state : DebtState D R ι) (u : Fin n → R),
    (∀ index, state.cache (x index) = some (u index)) →
    ∀ rest : (Fin n → R) → OracleComp (SourceCostSpec D R ι) β,
    (∀ values, Avoids (fun y => ∃ index, y = x index) (rest values)) →
    ∀ (g : (Fin n → R) → ℝ≥0∞) (budget : Nat),
    ∑' out, Pr[= out | interp tg initial model (Concrete.sequenceFin (fun index =>
          (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index))))) :
            OracleComp (SourceCostSpec D R ι) R)) >>= rest) budget state] *
        (if out.1.1.isSome then (Completeness.allSome (α := fun _ => R) fun index =>
          out.2.cache (x index)).elim 0 g else 0) ≤ g u
  | 0, x, _, _, state, u, _, rest, _, g, budget => by
      have hvalue : ∀ values : Fin 0 → Option R,
          ((Completeness.allSome (α := fun _ => R) values).elim 0 g : ℝ≥0∞) = g u := by
        intro values
        rw [Completeness.allSome, dif_pos fun index => index.elim0]
        exact congrArg g (funext fun index => index.elim0)
      rw [Concrete.sequenceFin, pure_bind]
      calc _ ≤ ∑' out, Pr[= out | interp tg initial model (rest Fin.elim0) budget state] * g u := by
            refine ENNReal.tsum_le_tsum fun out => mul_le_mul_right ?_ _
            split_ifs
            · rw [hvalue]
            · exact bot_le
        _ ≤ g u := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | n + 1, x, hx, hp, state, u, hc, rest, havoid, g, budget => by
      set tail : (Fin n → R) → OracleComp (SourceCostSpec D R ι) β := fun values =>
        rest (Fin.cases (u 0) values) with htail
      set reads : OracleComp (SourceCostSpec D R ι) (Fin n → R) := Concrete.sequenceFin fun index =>
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index.succ))))) :
          OracleComp (SourceCostSpec D R ι) R) with hreads
      have hsucc : ∀ index : Fin n, ¬x index.succ = x 0 := fun index heq =>
        Fin.succ_ne_zero index (hx heq)
      have havoid0 : Avoids (fun y => y = x 0) (reads >>= tail) :=
        avoids_bind _ (avoids_sequenceFin _ _ fun index => avoids_read _ _ (hsucc index))
          fun values => avoids_mono (fun y hy => ⟨0, hy⟩) (havoid _)
      have hstep : (Concrete.sequenceFin (fun index =>
          (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index))))) :
            OracleComp (SourceCostSpec D R ι) R)) >>= rest) =
          liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x 0))))) >>= fun head =>
            reads >>= fun values => rest (Fin.cases head values) := by
        rw [hreads, Concrete.sequenceFin]
        simp only [bind_assoc, pure_bind]
        rfl
      rw [hstep, interp_ordinary]
      split_ifs with hbudget
      · rw [ordinaryStep, hp 0]
        simp only
        rw [readOutside_cached (x 0) state (u 0) (hc 0), pure_bind, tsum_probOutput_map_mul]
        simp only
        have hcons : (Fin.cases (u 0) fun index : Fin n => u index.succ : Fin (n + 1) → R) = u := by
          funext index
          induction index using Fin.cases with
          | zero => rfl
          | succ index => rfl
        have hsub : ∀ values : Fin n → R,
            Avoids (fun y => ∃ index : Fin n, y = x index.succ) (tail values) := by
          intro values
          simp only [htail]
          refine avoids_mono (fun y hy => ?_) (havoid (Fin.cases (u 0) values))
          obtain ⟨index, hy⟩ := hy
          exact ⟨index.succ, hy⟩
        refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (le_of_le_of_eq
          (all_read_bound (fun index : Fin n => x index.succ)
            (fun a b heq => Fin.succ_injective n (hx heq)) (fun index => hp index.succ) state
            (fun index => u index.succ) (fun index => hc index.succ) tail hsub
            (fun values => g (Fin.cases (u 0) values)) (budget - 1)) (congrArg g hcons))
        by_cases hout : out ∈ support (interp tg initial model (reads >>= tail) (budget - 1) state)
        · have h0 := interp_avoids_cache tg initial model _ _ havoid0 (budget - 1) state out hout
            (x 0) rfl
          refine mul_le_mul_right ?_ _
          split_ifs
          · rw [allSome_cons _ (by rw [h0]; exact hc 0), elim_map]
          · exact le_rfl
        · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
      · rw [tsum_probOutput_pure_mul]
        simp

end FORS.Security.HiddenDebt

namespace FORS.Security.GraphView

variable [Params]

open FORS.Base
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

attribute [local instance] Classical.propDecidable

/-- The final assembly after its digest call. -/
noncomputable def finishRest (parameter : PublicParameter) (data : PublicData) (_message : Message)
    (randomness : Randomness) (digest : MessageDigest) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick (forsTrees * treeOpenCost)
  let index := digestIndex digest
  let some found ← sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)
    | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain => HiddenCost.reveal
    (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun κ => treeCostSource data index κ (digestLeaves digest κ)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

/-- Lifting a hash computation into the cost interface commutes with running a family in order. -/
theorem liftM_sequenceFin {α : Type} : ∀ {n : Nat} (computation : Fin n → OracleComp HashSpec α),
    (liftM (sequenceFin computation) : OracleComp CostSpec (Fin n → α)) =
      sequenceFin fun index => (liftM (computation index) : OracleComp CostSpec α)
  | 0, _ => by rw [sequenceFin, sequenceFin, liftM_pure]
  | _ + 1, computation => by
      rw [sequenceFin, sequenceFin]
      simp only [liftM_bind, liftM_pure, liftM_sequenceFin fun index => computation index.succ]

theorem finishCostSource_eq (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    finishCostSource parameter data message randomness =
      sequenceFin (fun call => (liftM (CostSpec.query (.inl (.inr (.inl
        (Security.digestInput parameter data.root message randomness call))))) :
          OracleComp CostSpec HashOutput)) >>=
        fun outputs => finishRest parameter data message randomness (truncateMessageDigest outputs) := by
  unfold finishCostSource finishRest messageDigest messageDigestCall
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind, liftM_sequenceFin]
  rfl

theorem msgInput_digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) :
    IsMsgInput (Security.digestInput parameter root message randomness call) :=
  ⟨parameter, call, _, rfl⟩

/-- A FORS opening reveals its secret and its leaf value, and reads the public path. -/
theorem avoids_treeCostSource (avoid : HashInput → Prop) (data : PublicData) (index : Index)
    (κ : FTree) (leaf : FLeaf) : Avoids avoid (treeCostSource data index κ leaf) := by
  unfold treeCostSource
  exact avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => avoids_pure _ _

theorem avoids_sequenceDep (avoid : HashInput → Prop) : ∀ {n : Nat} {α : Fin n → Type}
    {computation : (i : Fin n) → OracleComp CostSpec (Option (α i))},
    (∀ i, Avoids avoid (computation i)) → Avoids avoid (sequenceDep computation)
  | 0, _, _, _ => avoids_pure _ _
  | _ + 1, α, computation, h => by
      unfold sequenceDep
      refine avoids_bind _ (h 0) fun head => ?_
      rcases head with _ | head
      · exact avoids_pure _ _
      · refine avoids_bind _ (avoids_sequenceDep avoid (α := fun i => α i.succ) fun i => h i.succ)
          fun tail => ?_
        rcases tail with _ | tail <;> exact avoids_pure _ _

theorem avoids_layerCostSearch (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) : Avoids IsMsgInput (layerCostSearch parameter data index lay) := by
  unfold layerCostSearch layerSearch
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_liftHash _ _ (NoMsg.search _ _ _ _ _ _ _)) fun found => ?_
  rcases found with _ | pair
  · exact avoids_pure _ _
  · exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _

/-- The rest of the final assembly never queries a message-digest input. -/
theorem avoids_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    Avoids IsMsgInput (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_sequenceDep _ fun lay => avoids_layerCostSearch _ _ _ lay) fun found => ?_
  rcases found with _ | found
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_sequenceFin _ _ fun _ => avoids_reveal _ _)
      fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_treeCostSource _ _ _ _ _) fun _ => ?_
    exact avoids_pure _ _

theorem post_bind {spec : OracleSpec ι} {α β : Type} (P : β → Prop) (first : OracleComp spec α)
    {next : α → OracleComp spec β} (h : ∀ a, ∀ v ∈ support (next a), P v) :
    ∀ v ∈ support (first >>= next), P v := by
  intro v hv
  rw [support_bind] at hv
  obtain ⟨a, _, hva⟩ := Set.mem_iUnion₂.1 hv
  exact h a v hva

/-- A completed assembly signs with the trial's randomizer. -/
theorem finish_randomness (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    ∀ v ∈ support (finishCostSource parameter data message randomness), ∀ sig, v = some sig →
      sig.randomness = randomness := by
  rw [finishCostSource_eq]
  refine post_bind _ _ fun a => ?_
  unfold finishRest
  refine post_bind _ _ fun _ => post_bind _ _ fun found => ?_
  rcases found with _ | found
  · intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
  · refine post_bind _ _ fun _ => post_bind _ _ fun _ => ?_
    intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
    rfl

/-- The digest blocks of a message with a randomizer: one input per digest call. -/
abbrev pblk (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (call : DigestCall) : HashInput :=
  Security.digestInput parameter data.root message randomness call

/-- Distinct calls of a pair query distinct inputs. -/
theorem pblk_injective (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) : Function.Injective (pblk parameter data message randomness) := by
  intro call call' heq
  simpa using hashFields_injective (left := .message call) (right := .message call') trivial trivial
    (tweakableInput_injective heq).1

/-- The blocks of a pair, once the run has cached them all. -/
noncomputable def pcache (parameter : PublicParameter) (data : PublicData) (message : Message)
    (state : DebtState HashInput HashOutput Coordinate) (randomness : Randomness) :
    Option (DigestCall → HashOutput) :=
  Completeness.allSome (α := fun _ => HashOutput) fun call =>
    state.cache (pblk parameter data message randomness call)

/-- The kept view of a digest, read from its blocks. -/
def viewOf (u : DigestCall → HashOutput) : Lifetime.KeptDigestView :=
  Lifetime.localDigestView (truncateMessageDigest u)

section FinishOne

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Final assembly from a cached pair.** -/
theorem finish_boundAll (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness)
    (hparse : ∀ call, model.parse (pblk parameter data message randomness call) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput)
    (hc : ∀ call, state.cache (pblk parameter data message randomness call) = some (u call))
    (g : (DigestCall → HashOutput) → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (if out.1.1.isSome then (pcache parameter data message out.2 randomness).elim 0 g else 0) ≤ g u := by
  simp only [pcache]
  rw [finishCostSource_eq]
  exact all_read_bound tg initial model _ (pblk_injective parameter data message randomness) hparse
    state u hc (fun outputs => finishRest parameter data message randomness (truncateMessageDigest outputs))
    (fun _ => avoids_mono (fun x hx => by
        obtain ⟨call, rfl⟩ := hx
        exact msgInput_digestInput parameter data.root message randomness call)
      (avoids_finishRest parameter data message randomness _)) g budget

end FinishOne

/-- The fresh landed view law: weighting a fresh pair by a landed view weight gives the landing
probability times the uniform average of the weight. -/
theorem fresh_view_mean (parameter : PublicParameter) (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0)) =
      ForsPrice.landing * Domination.freshAvg Finset.univ gf := by
  classical
  set φ : MessageDigest → ℝ≥0∞ := fun digest =>
    if Landed parameter (digestIndex digest) then gf (Lifetime.localDigestView digest) else 0
  have hsplit : (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0)) =
      ∑' digest, Pr[= digest | truncateMessageDigest <$>
        ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] * φ digest := by
    rw [tsum_probOutput_map_mul]
    refine tsum_congr fun u => ?_
    simp only [φ, viewOf, digestIndex_truncate]
  rw [hsplit]
  have huni : ∀ digest, Pr[= digest | truncateMessageDigest <$>
      ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] =
      Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
    intro digest
    rw [probOutput_def, probOutput_def, Security.evalDist_digestBlock_uniform]
  simp only [huni]
  have hview : ∀ digest, φ digest = ∑ view, gf view *
      (if Landed parameter (digestIndex digest) ∧ Lifetime.localDigestView digest = view then 1 else 0) := by
    intro digest
    simp only [φ]
    split_ifs with hl
    · rw [Finset.sum_eq_single (Lifetime.localDigestView digest)]
      · simp [hl]
      · intro b _ hb
        simp [hl, Ne.symm hb]
      · simp
    · simp [hl]
  simp only [hview, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hterm : ∀ view : Lifetime.KeptDigestView,
      (∑' digest, Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] *
        (gf view * if Landed parameter (digestIndex digest) ∧ Lifetime.localDigestView digest = view then 1 else 0)) =
      gf view * (ForsPrice.landing * (Fintype.card Lifetime.KeptDigestView : ℝ≥0∞)⁻¹) := by
    intro view
    have hp := Lifetime.probEvent_landed_localDigest parameter (fun v => v = view)
    rw [probEvent_eq_tsum_ite] at hp
    rw [probEvent_eq_eq_probOutput, probOutput_uniformSample] at hp
    calc _ = gf view * ∑' digest, (if Landed parameter (digestIndex digest) ∧
            Lifetime.localDigestView digest = view then Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)]
            else 0) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun digest => ?_
          split_ifs <;> ring
      _ = _ := by rw [hp]; rfl
  simp only [hterm]
  rw [← Finset.sum_mul, Domination.freshAvg, Finset.card_univ]
  ring

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- The block of the signed message that carries the index. A trial reads it alone; the rest of its
pair follows only in the final assembly, once it has landed. -/
abbrev blk (randomness : Randomness) : HashInput :=
  pblk parameter data message randomness firstCall

/-- Weight of a selected pair with known blocks: fresh pairs (relative to the reference state)
use `gf` (landed only), pool pairs use `gp`. -/
noncomputable def pairWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (randomness : Randomness) (u : DigestCall → HashOutput) : ℝ≥0∞ :=
  if reference.cache (blk parameter data message randomness) = none then
    (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0)
  else gp randomness (viewOf u)

/-- Weight of a signing outcome: the weight of the pair it signed. -/
noncomputable def outWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  match out.1.1 with
  | some (some sig) => (pcache parameter data message out.2 sig.randomness).elim 0
      (pairWeight parameter data message reference gf gp sig.randomness)
  | _ => 0

/-- Forecast weight of a cached landed pair of the reference state. -/
noncomputable def poolValue (reference : DebtState HashInput HashOutput Coordinate)
    (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) (randomness : Randomness) : ℝ≥0∞ :=
  (pcache parameter data message reference randomness).elim 0 fun u =>
    if Landed parameter (blockIndex (u firstCall)) then gp randomness (viewOf u) else 0

/-- The state differs from the reference only by rejected trial blocks. -/
def Related (reference state : DebtState HashInput HashOutput Coordinate) : Prop :=
  ∀ ρ, state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) ∨
    (reference.cache (blk parameter data message ρ) = none ∧ ∃ u,
      state.cache (blk parameter data message ρ) = some u ∧ ¬Landed parameter (blockIndex u))

/-- The state differs from the reference only by rejected trial blocks, except at one randomizer. -/
def RelatedOff (reference state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : Prop :=
  ∀ ρ', ρ' ≠ ρ → (state.cache (blk parameter data message ρ') = reference.cache (blk parameter data message ρ') ∨
    (reference.cache (blk parameter data message ρ') = none ∧ ∃ u,
      state.cache (blk parameter data message ρ') = some u ∧ ¬Landed parameter (blockIndex u)))

/-- Randomizers whose block is cached. -/
noncomputable def cachedCount (state : DebtState HashInput HashOutput Coordinate) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ) ≠ none).card

/-- Randomizers whose block is cached and lands: the pool of the message. -/
noncomputable def landedCount (state : DebtState HashInput HashOutput Coordinate) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => ∃ u0, state.cache (blk parameter data message ρ) = some u0 ∧
    Landed parameter (blockIndex u0)).card

theorem payload_randomness_injective (root : Digest) (message : Message) {ρ ρ' : Randomness}
    (h : messageDigestPayload root message ρ = messageDigestPayload root message ρ') : ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact bytesLE_injective hparts.2

theorem blk_ne_of_ne {ρ ρ' : Randomness} (h : ρ ≠ ρ') :
    blk parameter data message ρ ≠ blk parameter data message ρ' := fun heq =>
  h (payload_randomness_injective data.root message (tweakableInput_injective heq).2.2)

theorem related_store (reference state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (ρ : Randomness)
    (hs : state.cache (blk parameter data message ρ) = none) (u : HashOutput)
    (hu : ¬Landed parameter (blockIndex u)) :
    Related parameter data message reference (state.store (blk parameter data message ρ) u) := by
  have href : reference.cache (blk parameter data message ρ) = none := by
    rcases hrel ρ with h | ⟨h, _⟩
    · rw [← h]; exact hs
    · exact h
  intro ρ'
  by_cases hρ : ρ' = ρ
  · subst hρ
    exact Or.inr ⟨href, u, by simp [DebtState.store], hu⟩
  · rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ) u]
    exact hrel ρ'

/-- The weight of a completed assembly is the weight of its own pair. -/
theorem outWeight_finish_le (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (budget : ℕ) (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget state)) :
    outWeight parameter data message reference gf gp out ≤
      (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  unfold outWeight
  rcases hres : out.1.1 with _ | (_ | sig)
  · exact le_rfl
  · exact bot_le
  · have hmem := interp_result_mem tg initial model _ budget state out hout _ hres
    have hrand := finish_randomness parameter data message ρ _ hmem sig rfl
    simp only [Option.isSome_some, if_true]
    subst hrand
    exact le_rfl

theorem card_randomness : Fintype.card Randomness = 2 ^ 128 := HiddenDebt.card_digest

theorem landed_mass (parameter : PublicParameter) :
    ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then (1 : ℝ≥0∞) else 0) = ForsPrice.landing := by
  have h := fresh_view_mean parameter (fun _ => 1)
  rw [Domination.freshAvg_const _ Finset.univ_nonempty, mul_one] at h
  exact h

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then (0 : ℝ≥0∞) else 1) = 1 - ForsPrice.landing := by
  have htot : (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then (1 : ℝ≥0∞) else 0)) +
    ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then (0 : ℝ≥0∞) else 1) = 1 := by
    rw [← ENNReal.tsum_add]
    calc _ = ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] := by
          refine tsum_congr fun u => ?_
          split_ifs <;> simp
      _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
  rw [landed_mass parameter] at htot
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)

/-! ### Fresh pairs completed by a signing call -/

/-- Weight of the reference-fresh landed pairs that a non-aborted signing call cached. -/
noncomputable def freshNewWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  if out.1.1.isSome then ∑ ρ : Randomness,
    (if reference.cache (blk parameter data message ρ) = none then
      (pcache parameter data message out.2 ρ).elim 0 fun u =>
        if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0
    else 0)
  else 0

/-- A final assembly keeps every message-digest entry but the blocks of its own pair. -/
theorem finish_keeps_msg (ρ : Randomness) (b : ℕ) (s' : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    ∀ x, IsMsgInput x → (∀ call, x ≠ pblk parameter data message ρ call) →
      out.2.cache x = s'.cache x := by
  intro x hmsg hne
  refine interp_avoids_cache tg initial model
    (fun x => IsMsgInput x ∧ ∀ call, x ≠ pblk parameter data message ρ call) _ ?_ b s' out hout x
    ⟨hmsg, hne⟩
  rw [finishCostSource_eq]
  exact avoids_bind _ (avoids_sequenceFin _ _ fun call => avoids_read _ _ fun h => h.2 call rfl)
    fun _ => avoids_mono (fun _ hx => hx.1) (avoids_finishRest parameter data message ρ _)

end Loop

end FORS.Security.GraphView
