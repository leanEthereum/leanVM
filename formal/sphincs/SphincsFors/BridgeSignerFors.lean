import SphincsFors.BridgeSigner
import SphincsFors.BridgeGroup

/-! The grinding signer's view of message-digest blocks. Its encoding search and its reveals
never query a message-digest input, so after the two digest calls of the final assembly the
selected pair's blocks are what the signature discloses. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.ForsSigner

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
  rintro ⟨parameter', call, payload', heq⟩
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

end SphincsFors.Security.ForsSigner

namespace SphincsFors.Security.GraphView

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

attribute [local instance] Classical.propDecidable

variable [Params]

/-- The final assembly after its two digest calls. -/
noncomputable def finishRest (parameter : PublicParameter) (data : PublicData) (_message : Message)
    (randomness : Randomness) (digest : MessageDigest) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick 122569
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forsKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let secrets ← sequenceFin fun tree => HiddenCost.reveal
    (.ftsSecret index tree (digestLeaves digest tree))
  HiddenCost.tick (152 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, secrets, data.forsPath index (digestLeaves digest),
    Fin.cases top (fun i => Fin.elim0 i)⟩

theorem finishCostSource_eq (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    finishCostSource parameter data message randomness =
      liftM (CostSpec.query (.inl (.inr (.inl (Security.digestInput parameter data.root message randomness 0))))) >>=
        fun first => liftM (CostSpec.query (.inl (.inr (.inl
          (Security.digestInput parameter data.root message randomness 1))))) >>= fun second =>
            finishRest parameter data message randomness (truncateMessageDigest first second) := by
  unfold finishCostSource finishRest messageDigest messageDigestCall
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

omit [Params] in
theorem msgInput_digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) :
    IsMsgInput (Security.digestInput parameter root message randomness call) :=
  ⟨parameter, call, _, rfl⟩

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
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
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
  refine post_bind _ _ fun a => post_bind _ _ fun b => ?_
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

omit [Params] in
theorem digestInput_ne (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    Security.digestInput parameter root message randomness 0 ≠ Security.digestInput parameter root message randomness 1 :=
  fun h => absurd (Security.digestInput_injective parameter root message randomness h) (by decide)

section FinishTwo

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Final assembly, both blocks.** -/
theorem finish_bound₂ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness)
    (hparse : ∀ call, model.parse (Security.digestInput parameter data.root message randomness call) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (Security.digestInput parameter data.root message randomness 0) = some u0)
    (g : HashOutput → HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (if out.1.1.isSome then
          (out.2.cache (Security.digestInput parameter data.root message randomness 0)).elim 0 (fun a =>
            (out.2.cache (Security.digestInput parameter data.root message randomness 1)).elim 0 (g a)) else 0) ≤
      (state.cache (Security.digestInput parameter data.root message randomness 1)).elim
        (∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * g u0 u) (g u0) := by
  rw [finishCostSource_eq]
  exact two_reads_bound₂ tg initial model _ _ (digestInput_ne parameter data.root message randomness)
    (hparse 0) (hparse 1) state u0 hc0
    (fun a b => finishRest parameter data message randomness (truncateMessageDigest a b))
    (fun a b => avoids_mono (fun x hx => by
        rcases hx with rfl | rfl
        · exact msgInput_digestInput parameter data.root message randomness 0
        · exact msgInput_digestInput parameter data.root message randomness 1)
      (avoids_finishRest parameter data message randomness _)) g budget

end FinishTwo

theorem signCostSourceWalk_succ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : ℕ) (randomness : Randomness) :
    signCostSourceWalk parameter data message (attempts + 1) randomness =
      liftM (CostSpec.query (.inl (.inr (.inl
        (Security.digestInput parameter data.root message randomness 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message randomness
          else signCostSourceWalk parameter data message attempts (randomness + 1) := by
  rw [signCostSourceWalk]
  rfl

omit [Params] in
/-- A walk of fewer than `2^128` steps does not come back. -/
theorem succ_iterate (y : Randomness) (j : ℕ) :
    (fun x : Randomness => x + 1)^[j] y = y + BitVec.ofNat digestBits j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hd : (2 : ℕ) ^ digestBits = 2 ^ 128 := rfl
      have h1 : (1 : Randomness).toNat = 1 := rfl
      rw [hd, h1]
      omega

omit [Params] in
theorem succ_iterate_ne (y : Randomness) (j : ℕ) (hj : j + 1 < 2 ^ 128) :
    (fun x : Randomness => x + 1)^[j] (y + 1) ≠ y := by
  rw [succ_iterate]
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  have hd : (2 : ℕ) ^ digestBits = 2 ^ 128 := rfl
  have h1 : (1 : Randomness).toNat = 1 := rfl
  rw [hd, h1] at h2
  have h3 : y.toNat < 2 ^ 128 := y.isLt
  omega

/-- The fresh landed view law: weighting both fresh blocks by a landed view weight gives the
landing probability times the uniform average of the weight. -/
theorem fresh_view_mean (parameter : PublicParameter) (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] * ∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then gf (Lifetime.localDigestView (truncateMessageDigest u0 u1)) else 0)) =
      ForsPrice.landing * Domination.freshAvg Finset.univ gf := by
  classical
  set φ : MessageDigest → ℝ≥0∞ := fun digest =>
    if Landed parameter (digestIndex digest) then gf (Lifetime.localDigestView digest) else 0
  have hsplit : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then gf (Lifetime.localDigestView (truncateMessageDigest u0 u1)) else 0)) =
      ∑' digest, Pr[= digest | (do
        let first ← ($ᵗ HashOutput : ProbComp HashOutput)
        let second ← ($ᵗ HashOutput : ProbComp HashOutput)
        pure (truncateMessageDigest first second))] * φ digest := by
    rw [tsum_probOutput_bind_mul]
    refine tsum_congr fun u0 => ?_
    congr 1
    rw [tsum_probOutput_bind_mul]
    refine tsum_congr fun u1 => ?_
    rw [tsum_probOutput_pure_mul]
    simp only [φ, digestIndex_truncate]
  rw [hsplit]
  have huni : ∀ digest, Pr[= digest | (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second))] = Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
    intro digest
    rw [probOutput_def, probOutput_def, Security.evalDist_digestBlocks_uniform]
  simp only [huni]
  -- regroup by kept view
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

omit [Params] in
/-- The fixed point of one grinding trial: cached items, cached rejections and fresh trials. -/
theorem loop_arith (a S w l F N u : ℝ≥0∞) (ha : a ≠ ⊤) (hS : S ≠ ⊤) (hw : w ≠ ⊤) (hFN : F + N ≤ 1)
    (hl : l ≤ 1) (hu : u ≤ w * F * l) :
    u * S + N * (a + w * S) + F * (l * a + (1 - l) * (a + w * S)) ≤ a + w * S := by
  have hF : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hFN)
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self hFN)
  have hlt : l ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hl
  have hut : u ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hu
  have hl1 : (1 - l).toReal = 1 - l.toReal := by
    rw [ENNReal.toReal_sub_of_le hl ENNReal.one_ne_top, ENNReal.toReal_one]
  have hwS : w * S ≠ ⊤ := ENNReal.mul_ne_top hw hS
  have haw : a + w * S ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ha, hwS⟩
  have hla : l * a ≠ ⊤ := ENNReal.mul_ne_top hlt ha
  have hl1t : (1 - l) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hlaw : (1 - l) * (a + w * S) ≠ ⊤ := ENNReal.mul_ne_top hl1t haw
  have hin : l * a + (1 - l) * (a + w * S) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hla, hlaw⟩
  have h1 : u * S ≠ ⊤ := ENNReal.mul_ne_top hut hS
  have h2 : N * (a + w * S) ≠ ⊤ := ENNReal.mul_ne_top hN haw
  have h3 : F * (l * a + (1 - l) * (a + w * S)) ≠ ⊤ := ENNReal.mul_ne_top hF hin
  have h12 : u * S + N * (a + w * S) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h1, h2⟩
  have hwF : w * F * l ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hw hF) hlt
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨h12, h3⟩) haw]
  rw [← ENNReal.toReal_le_toReal hut hwF] at hu
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hF, hN⟩) ENNReal.one_ne_top,
    ENNReal.toReal_add hF hN, ENNReal.toReal_one] at hFN
  rw [← ENNReal.toReal_le_toReal hlt ENNReal.one_ne_top, ENNReal.toReal_one] at hl
  rw [ENNReal.toReal_add h12 h3, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_add hla hlaw, ENNReal.toReal_mul, ENNReal.toReal_mul, hl1,
    ENNReal.toReal_add ha hwS, ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hu
  have h0a := ENNReal.toReal_nonneg (a := a)
  have h0S := ENNReal.toReal_nonneg (a := S)
  have h0w := ENNReal.toReal_nonneg (a := w)
  have h0F := ENNReal.toReal_nonneg (a := F)
  have h0N := ENNReal.toReal_nonneg (a := N)
  have h0l := ENNReal.toReal_nonneg (a := l)
  nlinarith [mul_nonneg h0a (by linarith : (0 : ℝ) ≤ 1 - N.toReal - F.toReal),
    mul_nonneg h0S (mul_nonneg h0w (by linarith : (0 : ℝ) ≤ 1 - N.toReal - F.toReal)),
    mul_nonneg h0S (by linarith : (0 : ℝ) ≤ w.toReal * F.toReal * l.toReal - u.toReal)]

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- Block `call` of the digest pair of the signed message with a randomizer. -/
abbrev blk (randomness : Randomness) (call : Fin 2) : HashInput :=
  Security.digestInput parameter data.root message randomness call

/-- The kept view of two digest blocks. -/
def viewOf (u0 u1 : HashOutput) : Lifetime.KeptDigestView :=
  Lifetime.localDigestView (truncateMessageDigest u0 u1)

/-- Weight of a selected pair with known blocks: fresh pairs (relative to the reference state)
use `gf` (landed only), pool pairs use `gp`. -/
noncomputable def pairWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (randomness : Randomness) (u0 u1 : HashOutput) : ℝ≥0∞ :=
  if reference.cache (blk parameter data message randomness 0) = none then
    (if Landed parameter (blockIndex u0) then gf (viewOf u0 u1) else 0)
  else gp randomness (viewOf u0 u1)

/-- Weight of a signing outcome: the weight of the pair it signed. -/
noncomputable def outWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  match out.1.1 with
  | some (some sig) => (out.2.cache (blk parameter data message sig.randomness 0)).elim 0 fun u0 =>
      (out.2.cache (blk parameter data message sig.randomness 1)).elim 0
        (pairWeight parameter data message reference gf gp sig.randomness u0)
  | _ => 0

/-- Forecast weight of a cached landed pair of the reference state. -/
noncomputable def poolValue (reference : DebtState HashInput HashOutput Coordinate)
    (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) (randomness : Randomness) : ℝ≥0∞ :=
  (reference.cache (blk parameter data message randomness 0)).elim 0 fun u0 =>
    if Landed parameter (blockIndex u0) then
      (reference.cache (blk parameter data message randomness 1)).elim
        (∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gp randomness (viewOf u0 u))
        (fun u1 => gp randomness (viewOf u0 u1))
    else 0

/-- The state differs from the reference only by rejected trial blocks. -/
def Related (reference state : DebtState HashInput HashOutput Coordinate) : Prop :=
  (∀ ρ, state.cache (blk parameter data message ρ 1) = reference.cache (blk parameter data message ρ 1)) ∧
  (∀ ρ, state.cache (blk parameter data message ρ 0) = reference.cache (blk parameter data message ρ 0) ∨
    (reference.cache (blk parameter data message ρ 0) = none ∧ ∃ u,
      state.cache (blk parameter data message ρ 0) = some u ∧ ¬Landed parameter (blockIndex u)))

/-- Randomizers whose block 0 is cached. -/
noncomputable def cachedCount (state : DebtState HashInput HashOutput Coordinate) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ 0) ≠ none).card

omit [Params] in
theorem payload_randomness_injective (root : Digest) (message : Message) {ρ ρ' : Randomness}
    (h : messageDigestPayload root message ρ = messageDigestPayload root message ρ') : ρ = ρ' := by
  exact bytesLE_injective (List.append_cancel_left h)

theorem related_store (reference state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (ρ : Randomness)
    (hs : state.cache (blk parameter data message ρ 0) = none) (u : HashOutput)
    (hu : ¬Landed parameter (blockIndex u)) :
    Related parameter data message reference (state.store (blk parameter data message ρ 0) u) := by
  have href : reference.cache (blk parameter data message ρ 0) = none := by
    rcases hrel.2 ρ with h | ⟨h, _⟩
    · rw [← h]; exact hs
    · exact h
  refine ⟨fun ρ' => ?_, fun ρ' => ?_⟩
  · rw [store_cache_ne state _ _ (fun h => by
      have := (tweakableInput_injective h).1
      simp [hashDomainFields, tweakFields] at this) u]
    exact hrel.1 ρ'
  · by_cases hρ : ρ' = ρ
    · subst hρ
      exact Or.inr ⟨href, u, by simp [DebtState.store], hu⟩
    · have hne : blk parameter data message ρ' 0 ≠ blk parameter data message ρ 0 := fun h =>
        hρ (by
          exact payload_randomness_injective data.root message (tweakableInput_injective h).2.2)
      rw [store_cache_ne state _ _ hne u]
      exact hrel.2 ρ'

omit [Params] in
theorem cachedCount_store (state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) (u : HashOutput) :
    cachedCount parameter data message (state.store (blk parameter data message ρ 0) u) ≤
      cachedCount parameter data message state + 1 := by
  unfold cachedCount
  calc (Finset.univ.filter fun ρ' : Randomness =>
          (state.store (blk parameter data message ρ 0) u).cache (blk parameter data message ρ' 0) ≠ none).card
      ≤ (insert ρ (Finset.univ.filter fun ρ' : Randomness =>
          state.cache (blk parameter data message ρ' 0) ≠ none)).card := by
        refine Finset.card_le_card fun ρ' hρ' => ?_
        rw [Finset.mem_filter] at hρ'
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : ρ' = ρ
        · exact Or.inl h
        · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
          have hne : blk parameter data message ρ' 0 ≠ blk parameter data message ρ 0 := fun heq =>
            h (payload_randomness_injective data.root message (tweakableInput_injective heq).2.2)
          rw [store_cache_ne state _ _ hne u] at hρ'
          exact hρ'.2
    _ ≤ _ := Finset.card_insert_le _ _

/-- The weight of a completed assembly is the weight of its own pair. -/
theorem outWeight_finish_le (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (budget : ℕ) (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget state)) :
    outWeight parameter data message reference gf gp out ≤
      (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ 0)).elim 0 (fun a =>
        (out.2.cache (blk parameter data message ρ 1)).elim 0
          (pairWeight parameter data message reference gf gp ρ a)) else 0) := by
  unfold outWeight
  rcases hres : out.1.1 with _ | (_ | sig)
  · exact le_rfl
  · exact bot_le
  · have hmem := interp_result_mem tg initial model _ budget state out hout _ hres
    have hrand := finish_randomness parameter data message ρ _ hmem sig rfl
    simp only [Option.isSome_some, if_true]
    subst hrand
    exact le_rfl

/-- **One grinding trial.** -/
theorem trial_bound
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (ρ : Randomness)
    (hih : ∀ s', (s' = state ∨ ∃ u, ¬Landed parameter (blockIndex u) ∧
        state.cache (blk parameter data message ρ 0) = none ∧ s' = state.store (blk parameter data message ρ 0) u) →
      ∀ b, ∑' out, Pr[= out | interp tg initial model cont b s'] *
          outWeight parameter data message reference gf gp out ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        outWeight parameter data message reference gf gp out ≤
      (state.cache (blk parameter data message ρ 0)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      s'.cache (blk parameter data message ρ 0) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          outWeight parameter data message reference gf gp out ≤
        (s'.cache (blk parameter data message ρ 1)).elim
          (∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            pairWeight parameter data message reference gf gp ρ u0 u)
          (pairWeight parameter data message reference gf gp ρ u0) := by
    intro s' u0 b hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₂ tg initial model parameter data message ρ
      (hparse ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (outWeight_finish_le tg initial model parameter data message reference gf gp ρ b s'
        out hout) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ 0]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ 0) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ 0) = some u0 := by
            rcases hrel.2 ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          refine le_trans (hfinish state u0 _ hc) (le_of_eq ?_)
          have hpw : pairWeight parameter data message reference gf gp ρ u0 = fun u1 => gp ρ (viewOf u0 u1) := by
            funext u1
            simp [pairWeight, href]
          rw [hpw]
          simp only [poolValue, href, Option.elim, if_pos hl, hrel.1 ρ]
        · rw [if_neg hl, if_neg hl]
          exact hih state (Or.inl rfl) _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ 0) = none := by
          rcases hrel.2 ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        have hb1 : state.cache (blk parameter data message ρ 1) = none := by
          rw [hrel.1 ρ]; exact hnob1 ρ href
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (by simp [DebtState.store])) (le_of_eq ?_)
          have hne : blk parameter data message ρ 1 ≠ blk parameter data message ρ 0 :=
            Ne.symm (digestInput_ne parameter data.root message ρ)
          rw [store_cache_ne state _ _ hne u0, hb1]
          simp only [Option.elim, pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (Or.inr ⟨u0, hl, hc, rfl⟩) _
  · rw [tsum_probOutput_pure_mul]
    simp only [outWeight]
    exact bot_le

omit [Params] in
theorem card_randomness : Fintype.card Randomness = 2 ^ 128 := HiddenDebt.card_digest

theorem landed_mass (parameter : PublicParameter) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0) = ForsPrice.landing := by
  have h := fresh_view_mean parameter (fun _ => 1)
  rw [Domination.freshAvg_const _ Finset.univ_nonempty, mul_one] at h
  rw [← h]
  refine tsum_congr fun u0 => ?_
  congr 1
  split_ifs
  · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]
  · simp

/-- One fresh trial: a landed uniform view with the landing probability, the continuation
otherwise. -/
theorem fresh_trial_eq (gf : Lifetime.KeptDigestView → ℝ≥0∞) (bound : ℝ≥0∞) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u') else bound) =
      ForsPrice.landing * Domination.freshAvg Finset.univ gf + (1 - ForsPrice.landing) * bound := by
  have hsplit : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u') else bound) =
      (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            gf (Lifetime.localDigestView (truncateMessageDigest u0 u')) else 0)) +
      bound * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then 0 else 1) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun u0 => ?_
    split_ifs
    · simp [viewOf]
    · simp [mul_comm]
  have hland := landed_mass parameter
  have hcompl : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - ForsPrice.landing := by
    have htot : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
      ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
      rw [← ENNReal.tsum_add]
      calc _ = ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] := by
            refine tsum_congr fun u0 => ?_
            split_ifs <;> simp
        _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
    rw [hland] at htot
    exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)
  rw [hsplit, hcompl, fresh_view_mean parameter gf]
  ring

/-- Statuses of the randomizers of the message in a state: unqueried, queried without landing, or
landed with the view of its two blocks. -/
noncomputable def stat (s : DebtState HashInput HashOutput Coordinate) :
    Walk.St Randomness Lifetime.KeptDigestView := fun ρ =>
  (s.cache (blk parameter data message ρ 0)).map fun u0 =>
    if Landed parameter (blockIndex u0) then
      some ((s.cache (blk parameter data message ρ 1)).elim (viewOf u0 u0) (viewOf u0))
    else none

/-- What the walk pays where it stops: the landed uniform view weight at an unqueried value, the
pool weight at a known landed one. -/
noncomputable def walkPay (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) : ℝ≥0∞ :=
  match stat parameter data message reference ρ with
  | none => Domination.freshAvg Finset.univ gf
  | some none => 0
  | some (some v) => gp ρ v

/-- **The walk from a start.** Its expected weight is the walk value over the statuses of the
reference state: the selection law of `R0, R0 + 1, ...` is exact. -/
theorem walk_bound
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts ρ budget state, attempts ≤ 2 ^ 128 → Related parameter data message reference state →
      (∀ j, j < attempts → state.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] ρ) 0) =
        reference.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] ρ) 0)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts ρ) budget state] *
          outWeight parameter data message reference gf gp out ≤
        Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf ForsPrice.landing (stat parameter data message reference))
          (Walk.tOf ForsPrice.landing (stat parameter data message reference))
          (walkPay parameter data message reference gf gp) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro ρ budget state _ _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        outWeight parameter data message reference gf gp out ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      exact bot_le
  | succ attempts ih =>
      intro ρ budget state hatt hrel hpos
      set bound := Walk.val (fun x : Randomness => x + 1)
        (Walk.sOf ForsPrice.landing (stat parameter data message reference))
        (Walk.tOf ForsPrice.landing (stat parameter data message reference))
        (walkPay parameter data message reference gf gp) 0 attempts (ρ + 1) with hbound
      have hpos0 : state.cache (blk parameter data message ρ 0) = reference.cache (blk parameter data message ρ 0) :=
        hpos 0 (Nat.succ_pos _)
      have hih : ∀ s', (s' = state ∨ ∃ u, ¬Landed parameter (blockIndex u) ∧
          state.cache (blk parameter data message ρ 0) = none ∧ s' = state.store (blk parameter data message ρ 0) u) →
          ∀ b, ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts (ρ + 1)) b s'] *
            outWeight parameter data message reference gf gp out ≤ bound := by
        intro s' hs' b
        have hposS : ∀ j, j < attempts → state.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0) =
            reference.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0) := by
          intro j hj
          have := hpos (j + 1) (Nat.succ_lt_succ hj)
          simpa only [Function.iterate_succ_apply] using this
        rcases hs' with rfl | ⟨u, hu, hc, rfl⟩
        · exact ih (ρ + 1) b s' (by omega) hrel hposS
        · refine ih (ρ + 1) b _ (by omega) (related_store parameter data message reference state hrel ρ hc u hu)
            fun j hj => ?_
          have hne : (fun x : Randomness => x + 1)^[j] (ρ + 1) ≠ ρ := succ_iterate_ne ρ j (by omega)
          have hbl : blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0 ≠
              blk parameter data message ρ 0 := fun h =>
            hne (payload_randomness_injective data.root message (tweakableInput_injective h).2.2)
          rw [store_cache_ne state _ _ hbl u]
          exact hposS j hj
      rw [signCostSourceWalk_succ]
      refine le_trans (trial_bound tg initial model parameter data message hparse reference hnob1 gf gp bound
        state hrel _ ρ hih budget) ?_
      rw [hpos0]
      have hval : Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf ForsPrice.landing (stat parameter data message reference))
          (Walk.tOf ForsPrice.landing (stat parameter data message reference))
          (walkPay parameter data message reference gf gp) 0 (attempts + 1) ρ =
          Walk.sOf ForsPrice.landing (stat parameter data message reference) ρ *
            walkPay parameter data message reference gf gp ρ +
          Walk.tOf ForsPrice.landing (stat parameter data message reference) ρ * bound := rfl
      rw [hval]
      cases hc : reference.cache (blk parameter data message ρ 0) with
      | none =>
          have hσ : stat parameter data message reference ρ = none := by simp [stat, hc]
          simp only [Option.elim, Walk.sOf, Walk.tOf, walkPay, hσ]
          exact le_of_eq (fresh_trial_eq parameter gf bound)
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hlandb1 ρ u0 hc hl)
            have hσ : stat parameter data message reference ρ = some (some (viewOf u0 u1)) := by
              simp [stat, hc, hl, h1]
            simp only [if_pos hl, Walk.sOf, Walk.tOf, walkPay, hσ, one_mul, zero_mul, add_zero]
            simp [poolValue, hc, hl, h1]
          · have hσ : stat parameter data message reference ρ = some none := by simp [stat, hc, hl]
            simp only [if_neg hl, Walk.sOf, Walk.tOf, walkPay, hσ, one_mul, zero_mul, zero_add, le_refl]

/-- **The selection law of the grinding signer.** A uniform base, then the walk: the expected
weight of a signing call is the mean walk value over the starts. -/
theorem loop_bound
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (attempts : ℕ) (hatt : attempts ≤ 2 ^ 128) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget reference] *
        outWeight parameter data message reference gf gp out ≤
      ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ * ∑ ρ, Walk.val (fun x : Randomness => x + 1)
        (Walk.sOf ForsPrice.landing (stat parameter data message reference))
        (Walk.tOf ForsPrice.landing (stat parameter data message reference))
        (walkPay parameter data message reference gf gp) 0 attempts ρ := by
  unfold signCostSourceLoop
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ := by
    intro ρ
    rw [probOutput_uniformSample]
  simp only [hpr]
  rw [ENNReal.tsum_mul_left, tsum_fintype]
  refine mul_le_mul_right (Finset.sum_le_sum fun ρ _ => ?_) _
  exact walk_bound tg initial model parameter data message hparse reference hnob1 hlandb1 gf gp attempts ρ budget
    reference hatt ⟨fun _ => rfl, fun _ => Or.inl rfl⟩ fun _ _ => rfl

/-! ### Fresh pairs completed by a signing call -/

/-- Weight of the reference-fresh pairs whose block 1 a non-aborted signing call cached. -/
noncomputable def freshNewWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  if out.1.1.isSome then ∑ ρ : Randomness,
    (if reference.cache (blk parameter data message ρ 1) = none then
      (out.2.cache (blk parameter data message ρ 0)).elim 0 fun u0 =>
        (out.2.cache (blk parameter data message ρ 1)).elim 0 fun u1 =>
          if Landed parameter (blockIndex u0) then gf (viewOf u0 u1) else 0
    else 0)
  else 0

omit [Params] in
theorem blk_ne_of_ne (ρ ρ' : Randomness) (call call' : Fin 2) (h : ρ ≠ ρ' ∨ call ≠ call') :
    blk parameter data message ρ call ≠ blk parameter data message ρ' call' := by
  intro heq
  obtain ⟨hfields, -, hpayload⟩ := tweakableInput_injective heq
  rcases h with h | h
  · exact h (payload_randomness_injective data.root message hpayload)
  · apply h
    have := congrArg TweakFields.hi hfields
    simp only [hashDomainFields, tweakFields] at this
    exact Fin.ext (by
      have h1 := call.isLt
      have h2 := call'.isLt
      have := congrArg BitVec.toNat this
      simp at this
      omega)

theorem avoids_finish_other (ρ ρ' : Randomness) (call : Fin 2) (hne : blk parameter data message ρ' call ≠
      blk parameter data message ρ 0) (hne' : blk parameter data message ρ' call ≠ blk parameter data message ρ 1) :
    Avoids (fun x => x = blk parameter data message ρ' call) (finishCostSource parameter data message ρ) := by
  rw [finishCostSource_eq]
  refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun a => ?_⟩
  · cases hb; exact hne hx.symm
  · refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun b => ?_⟩
    · cases hb; exact hne' hx.symm
    · exact avoids_mono (fun x hx => hx ▸ msgInput_digestInput parameter data.root message ρ' call)
        (avoids_finishRest parameter data message ρ _)

theorem freshNewWeight_finish (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (ρ : Randomness) (budget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate)
    (hb1rel : ∀ ρ', state.cache (blk parameter data message ρ' 1) = reference.cache (blk parameter data message ρ' 1))
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget state)) :
    freshNewWeight parameter data message reference gf out ≤
      (if reference.cache (blk parameter data message ρ 1) = none then
        (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ 0)).elim 0 (fun a =>
          (out.2.cache (blk parameter data message ρ 1)).elim 0 fun u1 =>
            if Landed parameter (blockIndex a) then gf (viewOf a u1) else 0) else 0)
      else 0) := by
  unfold freshNewWeight
  split_ifs with hsome hfresh hfresh
  · rw [Finset.sum_eq_single ρ]
    · rw [if_pos hfresh]
    · intro ρ' _ hne
      have hkeep := interp_avoids_cache tg initial model _ _
        (avoids_finish_other parameter data message ρ ρ' 1 (blk_ne_of_ne parameter data message ρ' ρ 1 0
          (Or.inr (by decide))) (blk_ne_of_ne parameter data message ρ' ρ 1 1 (Or.inl hne))) budget state out hout
        (blk parameter data message ρ' 1) rfl
      rw [hkeep, hb1rel ρ']
      split_ifs with h
      · rw [h]
        cases out.2.cache (blk parameter data message ρ' 0) <;> rfl
      · rfl
    · intro h; exact absurd (Finset.mem_univ ρ) h
  · refine le_of_eq (Finset.sum_eq_zero fun ρ' _ => ?_)
    by_cases hne : ρ' = ρ
    · subst hne; rw [if_neg hfresh]
    · have hkeep := interp_avoids_cache tg initial model _ _
        (avoids_finish_other parameter data message ρ ρ' 1 (blk_ne_of_ne parameter data message ρ' ρ 1 0
          (Or.inr (by decide))) (blk_ne_of_ne parameter data message ρ' ρ 1 1 (Or.inl hne))) budget state out hout
        (blk parameter data message ρ' 1) rfl
      rw [hkeep, hb1rel ρ']
      split_ifs with h
      · rw [h]
        cases out.2.cache (blk parameter data message ρ' 0) <;> rfl
      · rfl
  · exact le_rfl
  · exact le_rfl

/-- **One trial, fresh pairs only.** -/
theorem trial_bound_fresh
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] *
          freshNewWeight parameter data message reference gf out ≤ bound)
    (ρ : Randomness) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        freshNewWeight parameter data message reference gf out ≤
      (state.cache (blk parameter data message ρ 0)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then 0 else bound) := by
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ 0]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ 0) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ 0) = some u0 := by
            rcases hrel.2 ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          have hb1 := hlandb1 ρ u0 href hl
          refine le_of_eq (ENNReal.tsum_eq_zero.2 fun out => ?_)
          change Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) (budget - 1) state] *
            freshNewWeight parameter data message reference gf out = 0
          by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) (budget - 1) state)
          · have := freshNewWeight_finish tg initial model parameter data message reference gf ρ _ state hrel.1 out hout
            rw [if_neg hb1] at this
            rw [nonpos_iff_eq_zero.1 this, mul_zero]
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul]
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ 0) = none := by
          rcases hrel.2 ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        have hb1r : reference.cache (blk parameter data message ρ 1) = none := hnob1 ρ href
        have hb1 : state.cache (blk parameter data message ρ 1) = none := by rw [hrel.1 ρ]; exact hb1r
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have hs0 : (state.store (blk parameter data message ρ 0) u0).cache (blk parameter data message ρ 0) = some u0 := by
            simp [DebtState.store]
          have hb1rel : ∀ ρ', (state.store (blk parameter data message ρ 0) u0).cache (blk parameter data message ρ' 1) =
              reference.cache (blk parameter data message ρ' 1) := by
            intro ρ'
            rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message ρ' ρ 1 0 (Or.inr (by decide))) u0]
            exact hrel.1 ρ'
          set g' : HashOutput → HashOutput → ℝ≥0∞ := fun a u1 =>
            if Landed parameter (blockIndex a) then gf (viewOf a u1) else 0 with hg'
          calc _ ≤ ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) (budget - 1)
                (state.store (blk parameter data message ρ 0) u0)] *
                (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ 0)).elim 0 (fun a =>
                  (out.2.cache (blk parameter data message ρ 1)).elim 0 (g' a)) else 0) := by
                refine ENNReal.tsum_le_tsum fun out => ?_
                by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ)
                  (budget - 1) (state.store (blk parameter data message ρ 0) u0))
                · have := freshNewWeight_finish tg initial model parameter data message reference gf ρ _ _ hb1rel out hout
                  rw [if_pos hb1r] at this
                  exact mul_le_mul_right this _
                · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
            _ ≤ _ := finish_bound₂ tg initial model parameter data message ρ (hparse ρ) _ u0 hs0 g' _
            _ = _ := by
                rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message ρ ρ 1 0 (Or.inr (by decide))) u0, hb1]
                simp only [Option.elim, hg', if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_store parameter data message reference state hrel ρ hc u0 hl) _
  · rw [tsum_probOutput_pure_mul]
    simp only [freshNewWeight, Option.isSome_none]
    exact bot_le

/-- Fresh pairs of the walk from any start. -/
theorem walk_bound_fresh
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts ρ budget state, Related parameter data message reference state →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts ρ) budget state] *
          freshNewWeight parameter data message reference gf out ≤ Domination.freshAvg Finset.univ gf := by
  set a := Domination.freshAvg Finset.univ gf with ha
  intro attempts
  induction attempts with
  | zero =>
      intro ρ budget state hrel
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        freshNewWeight parameter data message reference gf out ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      refine le_of_eq_of_le ?_ bot_le
      unfold freshNewWeight
      simp only [Option.isSome_some, if_true]
      refine Finset.sum_eq_zero fun ρ _ => ?_
      split_ifs with h
      · rw [hrel.1 ρ, h]
        cases state.cache (blk parameter data message ρ 0) <;> rfl
      · rfl
  | succ attempts ih =>
      intro ρ budget state hrel
      rw [signCostSourceWalk_succ]
      refine le_trans (trial_bound_fresh tg initial model parameter data message hparse reference hnob1
        hlandb1 gf a state hrel _ (fun s' hs' b => ih (ρ + 1) b s' hs') ρ budget) ?_
      have hland1 : ForsPrice.landing ≤ 1 := by
        unfold ForsPrice.landing
        exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)
      cases state.cache (blk parameter data message ρ 0) with
      | none =>
          simp only [Option.elim]
          rw [fresh_trial_eq parameter gf a, ← add_mul, add_tsub_cancel_of_le hland1, one_mul]
      | some u0 =>
          simp only [Option.elim]
          split_ifs
          · exact bot_le
          · exact le_rfl

/-- **Fresh pairs of the grinding signer.** Whatever the cache, the pairs a signing call completes
have, in total, at most the uniform landed-view weight. -/
theorem loop_bound_fresh
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts budget state, Related parameter data message reference state →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          freshNewWeight parameter data message reference gf out ≤ Domination.freshAvg Finset.univ gf := by
  intro attempts budget state hrel
  unfold signCostSourceLoop
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] * Domination.freshAvg Finset.univ gf :=
        ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right
          (walk_bound_fresh tg initial model parameter data message hparse reference hnob1 hlandb1 gf
            attempts ρ budget state hrel) _
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

end Loop

end SphincsFors.Security.GraphView
