import Sphincs.BridgeSignerForest
import Sphincs.BridgeInterpSupport

/-! What a completed signing call leaves behind in the lazy run: at most one selected pair with its
block cached, every other randomizer of the message unchanged or rejected, forest chain values
revealed only for the selected digest (at and above the opened positions), and, on failure, no
reveals and a failing index. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.GraphView

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A reveal is a forest chain value the digest opens, or not a forest chain value at all. -/
def ForestOk (digest : MessageDigest) (x : Coordinate) : Prop :=
  ∀ i c s j a ch pos, x = .fchain i c s j a ch pos →
    i = digestIndex digest ∧ s = (digestMarks digest c).super ∧ a = (digestMarks digest c).child j ∧
      (openedPos (digestMarks digest c) j ch).val ≤ pos.val

omit [Params] in
theorem revealsIn_coordCostSource (digest : MessageDigest) (data : PublicData) (c : Coord) :
    RevealsIn (D := HashInput) (R := HashOutput) (ForestOk digest)
      (coordCostSource data (digestIndex digest) c (digestMarks digest c)) := by
  unfold coordCostSource
  refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun j => ?_) fun _ => revealsIn_pure _ _
  refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun ch => ?_) fun _ => revealsIn_pure _ _
  unfold revealChainCost
  refine revealsIn_sequenceFin _ _ fun k => ?_
  split
  · rename_i hk
    refine revealsIn_reveal _ _ ?_
    intro i c' s j' a ch' pos h
    cases h
    exact ⟨rfl, rfl, rfl, hk⟩
  · exact revealsIn_pure _ _

theorem revealsIn_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    RevealsIn (D := HashInput) (R := HashOutput) (ForestOk digest)
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine revealsIn_bind _ (revealsIn_tick _ _) fun _ => ?_
  refine revealsIn_bind _ (revealsIn_liftHash _ _) fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact revealsIn_pure _ _
  · refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun chain => revealsIn_reveal _ _ ?_) fun _ => ?_
    · intro i c s j a ch pos h
      cases h
    refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun c => revealsIn_coordCostSource digest data c)
      fun _ => ?_
    exact revealsIn_bind _ (revealsIn_tick _ _) fun _ => revealsIn_pure _ _

omit [Params] in
theorem revealsIn_false_tick (amount : ℕ) :
    RevealsIn (D := HashInput) (R := HashOutput) (ι := Coordinate) (fun _ => False) (tick amount) :=
  revealsIn_tick _ _

section Finish

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

omit [Params] in
theorem no_reveals_of_false {α : Type} (computation : OracleComp CostSpec α)
    (h : RevealsIn (D := HashInput) (R := HashOutput) (fun _ => False) computation) (budget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model computation budget state)) : out.1.2.1 = [] := by
  rcases hr : out.1.2.1 with _ | ⟨c, rest⟩
  · rfl
  · exact absurd (interp_reveals tg initial model computation h budget state out hout c (by rw [hr]; simp)) id

/-- A failed final assembly reveals nothing. -/
theorem finishRest_none (randomness : Randomness) (digest : MessageDigest) (budget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishRest parameter data message randomness digest) budget state))
    (hnone : out.1.1 = some none) : out.1.2.1 = [] := by
  unfold finishRest at hout
  obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg initial model _ _ budget state out hout
  have hr1 := no_reveals_of_false tg initial model _ (revealsIn_false_tick _) _ _ o1 ho1
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, hrev2, _⟩
  · rw [hnone] at hn; cases hn
  rw [hrev2, hr1, List.nil_append]
  obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg initial model _ _ _ _ o2 ho2
  have hr3 := no_reveals_of_false tg initial model _ (revealsIn_liftHash _ _) _ _ o3 ho3
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, hrev4, _⟩
  · rw [hres2, hnone] at *; simp_all
  rw [hrev4, hr3, List.nil_append]
  rcases found with _ | ⟨counter, word⟩
  · change o4 ∈ support (interp tg initial model (pure none) _ _) at ho4
    rw [interp_pure, support_pure, Set.mem_singleton_iff] at ho4
    rw [ho4]
  · exfalso
    have hmem := interp_result_mem tg initial model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
    revert hmem
    dsimp only
    intro hmem
    refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
    intro v hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact fun h => by cases h

/-- **Final assembly, support.** -/
theorem finish_post (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (ρ : Randomness) (budget : ℕ) (s1 : DebtState HashInput HashOutput Coordinate)
    (hprep : Prepared initial s1) (u0 : HashOutput) (hc0 : s1.cache (blk parameter data message ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget s1))
    (r : Option Signature) (hr : out.1.1 = some r) :
    out.2.cache (blk parameter data message ρ) = some u0 ∧
      (∀ x, IsMsgInput x → out.2.cache x = s1.cache x) ∧
      (∀ c ∈ out.1.2.1, ForestOk (truncateMessageDigest u0) c) ∧
      (∀ sig, r = some sig → sig.randomness = ρ) ∧
      (r = none → out.1.2.1 = [] ∧ (Lifetime.localDigestView (truncateMessageDigest u0)).1 ∈ Fail) := by
  have hsig : ∀ sig, r = some sig → sig.randomness = ρ := by
    intro sig hsig
    have hmem := interp_result_mem tg initial model _ budget s1 out hout r hr
    exact finish_randomness parameter data message ρ r hmem sig hsig
  rw [finishCostSource_eq] at hout
  rw [interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse ρ] at hout
    simp only at hout
    rw [readOutside_cached _ s1 u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    simp only at hr ⊢
    have havoid := interp_avoids_cache tg initial model IsMsgInput _
      (avoids_finishRest parameter data message ρ (truncateMessageDigest u0)) _ s1 o ho
    refine ⟨?_, fun x hx => havoid x hx, ?_, hsig, ?_⟩
    · rw [havoid _ (msgInput_digestInput parameter data.root message ρ), hc0]
    · intro c hc
      exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data message ρ _) _ _ o ho c hc
    · intro hnone
      rw [hnone] at hr
      exact ⟨finishRest_none tg initial model parameter data message ρ _ _ _ o ho hr,
        hfail ρ _ _ s1 hprep o ho hr⟩
  · rw [support_pure, Set.mem_singleton_iff] at hout
    rw [hout] at hr
    cases hr

end Finish

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- One randomizer of the message: its block unchanged or a new rejected one. -/
def RelatedAt (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : Prop :=
  s'.cache (blk parameter data message ρ) = s.cache (blk parameter data message ρ) ∨
    (s.cache (blk parameter data message ρ) = none ∧ ∃ u,
      s'.cache (blk parameter data message ρ) = some u ∧ ¬Landed parameter (blockIndex u))

theorem RelatedAt.refl (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) :
    RelatedAt parameter data message s s ρ := Or.inl rfl

theorem RelatedAt.trans {s s' s'' : DebtState HashInput HashOutput Coordinate} {ρ : Randomness}
    (h : RelatedAt parameter data message s s' ρ) (h' : RelatedAt parameter data message s' s'' ρ) :
    RelatedAt parameter data message s s'' ρ := by
  rcases h' with h2 | ⟨h2n, u, hu, hnl⟩
  · rcases h with h1 | h1
    · exact Or.inl (h2.trans h1)
    · unfold RelatedAt; rw [h2]; exact Or.inr h1
  · rcases h with h1 | ⟨h1n, _, hu1, _⟩
    · exact Or.inr ⟨h1 ▸ h2n, u, hu, hnl⟩
    · rw [hu1] at h2n; cases h2n

/-- The selected pair of a completed signing call. -/
def Selected (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) (u0 : HashOutput) : Prop :=
  s'.cache (blk parameter data message ρ) = some u0 ∧ Landed parameter (blockIndex u0) ∧
  (s.cache (blk parameter data message ρ) = none ∨ s.cache (blk parameter data message ρ) = some u0) ∧
  ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data message s s' ρ'

/-- What a completed signing call leaves behind. -/
def SignPost (Fail : Finset (Fin (2 ^ subtreeHeight))) (s s' : DebtState HashInput HashOutput Coordinate)
    (reveals : List Coordinate) (r : Option Signature) : Prop :=
  (r = none ∧ reveals = [] ∧ ∀ ρ, RelatedAt parameter data message s s' ρ) ∨
  ∃ ρ u0, Selected parameter data message s s' ρ u0 ∧
    (∀ c ∈ reveals, ForestOk (truncateMessageDigest u0) c) ∧
    (∀ sig, r = some sig → sig.randomness = ρ) ∧
    (r = none → reveals = [] ∧ (s.cache (blk parameter data message ρ) = none →
      (Lifetime.localDigestView (truncateMessageDigest u0)).1 ∈ Fail))

end Loop

end Sphincs.Security.GraphView
