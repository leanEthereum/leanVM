import Sphincs.BridgeSigner

/-! The grinding signer's view of message-digest blocks, and its fair share. Its encoding search
and its reveals never query a message-digest input, so after the digest call of the final assembly
the selected pair's block is what the signature discloses. A cached landed pair of the signed
message is selected with probability at most `1 / (n + R)` when the message has `n` cached landed
pairs: every trial picks each of them with probability `2^-128` and a fresh landed pair with
probability at least `R · 2^-128`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForestSigner

open Concrete HiddenCost HiddenDebt GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A message-digest input, for any public parameter and payload. -/
def IsMsgInput (input : HashInput) : Prop :=
  ∃ parameter payload, input = tweakableHashInput parameter .message payload

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
  rintro ⟨parameter', payload', heq⟩
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
    (message : Digest) (counter : Counter) :
    NoMsg (Concrete.encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact NoMsg.bind (NoMsg.tweakableHash _ _ _ (by simp [hashDomainFields, tweakFields])) fun _ => NoMsg.pure' _

theorem NoMsg.search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : ∀ attempts start,
    NoMsg (ReferenceChoice.search parameter lay tree leaf message attempts start)
  | 0, _ => NoMsg.pure' _
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine NoMsg.bind (NoMsg.encode _ _ _ _ _ _) fun found => ?_
      cases found with
      | none => exact NoMsg.search parameter lay tree leaf message attempts (start + 1)
      | some _ => exact NoMsg.pure' _

end Sphincs.Security.ForestSigner

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

omit [Fintype ι] in
/-- **One read of a cached entry, kept.** -/
theorem one_read_bound {β : Type} (x0 : D) (hp0 : model.parse x0 = none)
    (state : DebtState D R ι) (u0 : R) (hc0 : state.cache x0 = some u0)
    (rest : R → OracleComp (SourceCostSpec D R ι) β)
    (havoid : ∀ a, Avoids (fun x => x = x0) (rest a)) (g : R → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← (interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x0)))) >>= fun a => rest a) budget state)}[x = out] *
        (if out.1.1.isSome then (out.2.cache x0).elim 0 g else 0) ≤ g u0 := by
  rw [interp_ordinary]
  split_ifs with h0
  · rw [ordinaryStep, hp0]
    simp only
    rw [readOutside_cached x0 state u0 hc0, pure_bind, OracleComp.tsum_prEvent_map_mul]
    simp only
    calc _ ≤ ∑' out, Pr{let x ← interp tg initial model (rest u0) (budget - 1) state}[x = out] * g u0 := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (rest u0) (budget - 1) state)
          · have hk0 := interp_avoids_cache tg initial model _ (rest u0) (havoid u0) _ state out hout x0 rfl
            gcongr
            split_ifs
            · rw [hk0, hc0]; rfl
            · exact bot_le
          · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
      _ ≤ g u0 := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
  · rw [OracleComp.tsum_prEvent_pure_mul]
    simp

end Sphincs.Security.HiddenDebt

namespace Sphincs.Security.GraphView

open SphincsFors.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner

attribute [local instance] Classical.propDecidable

variable [Params]

/-- The final assembly after its digest call. -/
noncomputable def finishRest (parameter : PublicParameter) (data : PublicData) (_message : Message)
    (randomness : Randomness) (digest : MessageDigest) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick 118081
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forestKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let opening ← sequenceFin fun c => coordCostSource data index c (digestMarks digest c)
  HiddenCost.tick (152 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, opening, Fin.cases top (fun i => Fin.elim0 i)⟩

theorem finishCostSource_eq (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    finishCostSource parameter data message randomness =
      liftM (CostSpec.query (.inl (.inr (.inl (Security.digestInput parameter data.root message randomness))))) >>=
        fun first => finishRest parameter data message randomness (truncateMessageDigest first) := by
  unfold finishCostSource finishRest messageDigest messageDigestCall
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

omit [Params] in
theorem msgInput_digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    IsMsgInput (Security.digestInput parameter root message randomness) :=
  ⟨parameter, _, rfl⟩

omit [Params] in
theorem avoids_coordCostSource (avoid : HashInput → Prop) (data : PublicData) (index : Index) (c : Coord)
    (mark : CoordMark) : Avoids avoid (coordCostSource data index c mark) := by
  unfold coordCostSource
  refine avoids_bind _ (avoids_sequenceFin _ _ fun j => ?_) fun _ => avoids_pure _ _
  refine avoids_bind _ (avoids_sequenceFin _ _ fun i => ?_) fun _ => avoids_pure _ _
  unfold revealChainCost
  refine avoids_sequenceFin _ _ fun k => ?_
  split
  · exact avoids_reveal _ _
  · exact avoids_pure _ _

/-- The rest of the final assembly never queries a message-digest input. -/
theorem avoids_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    Avoids IsMsgInput (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_liftHash _ _ (NoMsg.search _ _ _ _ _ _ _)) fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_coordCostSource _ _ _ _ _) fun _ => ?_
    exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _

omit [Params] in
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
  rcases found with _ | ⟨counter, word⟩
  · intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
  · refine post_bind _ _ fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_
    intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
    rfl

section FinishOne

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Final assembly, one cached block.** -/
theorem finish_bound₁ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness)
    (hparse : model.parse (Security.digestInput parameter data.root message randomness) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (Security.digestInput parameter data.root message randomness) = some u0)
    (g : HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (finishCostSource parameter data message randomness) budget state}[x = out] *
        (if out.1.1.isSome then
          (out.2.cache (Security.digestInput parameter data.root message randomness)).elim 0 g else 0) ≤ g u0 := by
  rw [finishCostSource_eq]
  exact one_read_bound tg initial model _ hparse state u0 hc0
    (fun a => finishRest parameter data message randomness (truncateMessageDigest a))
    (fun a => avoids_mono (fun x hx => by
        rw [hx]; exact msgInput_digestInput parameter data.root message randomness)
      (avoids_finishRest parameter data message randomness _)) g budget

end FinishOne

/-- The view of a digest block. -/
def viewOf (u0 : HashOutput) : Lifetime.KeptDigestView :=
  Lifetime.localDigestView (truncateMessageDigest u0)

/-- The fresh landed view law: weighting a fresh block by a landed view weight gives the landing
probability times the uniform average of the weight. -/
theorem fresh_view_mean (parameter : PublicParameter) (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    (∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) =
      ForestPrice.landing * Domination.freshAvg Finset.univ gf := by
  classical
  set φ : MessageDigest → ℝ≥0∞ := fun digest =>
    if Landed parameter (digestIndex digest) then gf (Lifetime.localDigestView digest) else 0
  have hsplit : (∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) =
      ∑' digest, Pr{let x ← truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)}[x = digest] * φ digest := by
    rw [OracleComp.tsum_prEvent_map_mul]
    refine tsum_congr fun u0 => ?_
    simp only [φ, viewOf, digestIndex_truncate]
  rw [hsplit]
  have huni : ∀ digest, Pr{let x ← truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)}[x = digest] =
      Pr{let x ← ($ᵗ MessageDigest : ProbComp MessageDigest)}[x = digest] := by
    intro digest
    exact Security.evalDist_digestBlock_uniform.prEvent_eq _
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
      (∑' digest, Pr{let x ← ($ᵗ MessageDigest : ProbComp MessageDigest)}[x = digest] *
        (gf view * if Landed parameter (digestIndex digest) ∧ Lifetime.localDigestView digest = view then 1 else 0)) =
      gf view * (ForestPrice.landing * (Fintype.card Lifetime.KeptDigestView : ℝ≥0∞)⁻¹) := by
    intro view
    have hp := Lifetime.probEvent_landed_localDigest parameter (fun v => v = view)
    rw [OracleComp.prEvent_eq_tsum_ite] at hp
    rw [SampleableType.prEvent_uniformSample_eq_singleton] at hp
    calc _ = gf view * ∑' digest, (if Landed parameter (digestIndex digest) ∧
            Lifetime.localDigestView digest = view then Pr{let x ← ($ᵗ MessageDigest : ProbComp MessageDigest)}[x = digest]
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

/-- The digest block of the signed message with a randomizer. -/
abbrev blk (randomness : Randomness) : HashInput :=
  Security.digestInput parameter data.root message randomness

/-- Weight of a selected pair with a known block: fresh pairs (relative to the reference state)
use `gf` (landed only), pool pairs use `gp`. -/
noncomputable def pairWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (randomness : Randomness) (u0 : HashOutput) : ℝ≥0∞ :=
  if reference.cache (blk parameter data message randomness) = none then
    (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)
  else gp randomness (viewOf u0)

/-- Weight of a signing outcome: the weight of the pair it signed. -/
noncomputable def outWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  match out.1.1 with
  | some (some sig) => (out.2.cache (blk parameter data message sig.randomness)).elim 0
      (pairWeight parameter data message reference gf gp sig.randomness)
  | _ => 0

/-- Forecast weight of a cached landed pair of the reference state. -/
noncomputable def poolValue (reference : DebtState HashInput HashOutput Coordinate)
    (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) (randomness : Randomness) : ℝ≥0∞ :=
  (reference.cache (blk parameter data message randomness)).elim 0 fun u0 =>
    if Landed parameter (blockIndex u0) then gp randomness (viewOf u0) else 0

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

omit [Params] in
theorem payload_randomness_injective (root : Digest) (message : Message) {ρ ρ' : Randomness}
    (h : messageDigestPayload root message ρ = messageDigestPayload root message ρ') : ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact bytesLE_injective hparts.2

omit [Params] in
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

omit [Params] in
theorem cachedCount_store (state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) (u : HashOutput) :
    cachedCount parameter data message (state.store (blk parameter data message ρ) u) ≤
      cachedCount parameter data message state + 1 := by
  unfold cachedCount
  calc (Finset.univ.filter fun ρ' : Randomness =>
          (state.store (blk parameter data message ρ) u).cache (blk parameter data message ρ') ≠ none).card
      ≤ (insert ρ (Finset.univ.filter fun ρ' : Randomness =>
          state.cache (blk parameter data message ρ') ≠ none)).card := by
        refine Finset.card_le_card fun ρ' hρ' => ?_
        rw [Finset.mem_filter] at hρ'
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : ρ' = ρ
        · exact Or.inl h
        · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
          rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message h) u] at hρ'
          exact hρ'.2
    _ ≤ _ := Finset.card_insert_le _ _

/-- The weight of a completed assembly is the weight of its own pair. -/
theorem outWeight_finish_le (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (budget : ℕ) (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget state)) :
    outWeight parameter data message reference gf gp out ≤
      (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  unfold outWeight
  rcases hres : out.1.1 with _ | (_ | sig)
  · exact le_rfl
  · exact bot_le
  · have hmem := interp_result_mem tg initial model _ budget state out hout _ hres
    have hrand := finish_randomness parameter data message ρ _ hmem sig rfl
    simp only [Option.isSome_some, ite_true]
    subst hrand
    exact le_rfl

omit [Params] in
theorem card_randomness : Fintype.card Randomness = 2 ^ 128 := HiddenDebt.card_digest

theorem landed_mass (parameter : PublicParameter) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0) = ForestPrice.landing := by
  have h := fresh_view_mean parameter (fun _ => 1)
  rw [Domination.freshAvg_const _ Finset.univ_nonempty, mul_one] at h
  exact h

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - ForestPrice.landing := by
  have htot : (∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
    rw [← ENNReal.tsum_add]
    calc _ = ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] := by
          refine tsum_congr fun u0 => ?_
          split_ifs <;> simp [-SampleableType.prEvent_uniformSample]
      _ = 1 := OracleComp.tsum_prEvent_eq_one _
  rw [landed_mass parameter] at htot
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)

/-! ### Fresh pairs completed by a signing call -/

/-- Weight of the reference-fresh landed pairs that a non-aborted signing call cached. -/
noncomputable def freshNewWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  if out.1.1.isSome then ∑ ρ : Randomness,
    (if reference.cache (blk parameter data message ρ) = none then
      (out.2.cache (blk parameter data message ρ)).elim 0 fun u0 =>
        if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0
    else 0)
  else 0

/-- A final assembly from a cached block keeps every message-digest entry. -/
theorem finish_keeps_msg (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none) (ρ : Randomness)
    (b : ℕ) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : s'.cache (blk parameter data message ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    ∀ x, IsMsgInput x → out.2.cache x = s'.cache x := by
  rw [finishCostSource_eq, interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse ρ] at hout
    simp only at hout
    rw [readOutside_cached _ s' u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    exact interp_avoids_cache tg initial model IsMsgInput _
      (avoids_finishRest parameter data message ρ (truncateMessageDigest u0)) _ s' o ho
  · rw [support_pure, Set.mem_singleton_iff] at hout
    rw [hout]
    exact fun _ _ => rfl

end Loop

end Sphincs.Security.GraphView
