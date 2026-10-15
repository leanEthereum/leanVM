import Sphincs.BridgeSignerPost
import Sphincs.BridgeVirtualMono
import Sphincs.BridgeImplication

/-! Ingredients of the forest potential of the lazy run. Every cached landed message-randomizer
pair is an item; the unsigned ones are candidates. This file defines the pairs, their views, the
item and disclosure invariants, the final value (a forest cover) and proves the facts about fresh
pairs, ordinary queries and signing calls that the one-coin potentials of
`BridgeForsPotentialOnce` and `BridgeForsGeneric` build on. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A message and a randomizer. -/
abbrev Pair := Message × Randomness

abbrev State := DebtState HashInput HashOutput Coordinate

noncomputable instance viewInhabited : Inhabited View := ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩

omit [Params] in
theorem payload_pair_injective (root : Digest) {m m' : Message} {ρ ρ' : Randomness}
    (h : messageDigestPayload root m ρ = messageDigestPayload root m' ρ') : m = m' ∧ ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparts.1, bytesLE_injective hparts.2⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- The digest block of a pair. -/
abbrev pblk (p : Pair) : HashInput := blk parameter data p.1 p.2

omit [Params] in
theorem pblk_injective {p q : Pair} (h : pblk parameter data p = pblk parameter data q) : p = q := by
  obtain ⟨-, -, hpayload⟩ := tweakableInput_injective h
  obtain ⟨hm, hρ⟩ := payload_pair_injective data.root hpayload
  exact Prod.ext hm hρ

omit [Params] in
theorem pblk_ne_of_ne {p q : Pair} (h : p ≠ q) : pblk parameter data p ≠ pblk parameter data q := fun heq =>
  h (pblk_injective parameter data heq)

/-- The kept view of a pair whose block is cached. -/
noncomputable def pview (s : State) (p : Pair) : View :=
  (s.cache (pblk parameter data p)).elim default viewOf

/-- The block of the pair is cached and lands. -/
def LandedIn (s : State) (p : Pair) : Prop :=
  ∃ u0, s.cache (pblk parameter data p) = some u0 ∧ Landed parameter (blockIndex u0)

/-- The items are exactly the landed pairs. -/
structure PInv (s : State) (P : List Pair) : Prop where
  nodup : P.Nodup
  mem : ∀ p, p ∈ P ↔ LandedIn parameter data s p

/-- The local index of a leaf index. -/
def localIdx (i : Index) : Fin (2 ^ subtreeHeight) := ⟨i.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem localDigestView_fst (digest : MessageDigest) :
    (Lifetime.localDigestView digest).1 = localIdx (digestIndex digest) := rfl

theorem localDigestView_snd (digest : MessageDigest) :
    (Lifetime.localDigestView digest).2 = coordField digest := rfl

/-- The disclosed views account for every revealed forest chain value: some disclosed view at its
index opens its chain at or below its position. -/
def DInv (R : List Coordinate) (d : Multiset View) : Prop :=
  ∀ i c s j a ch (pos : FPos), Coordinate.fchain i c s j a ch pos ∈ R →
    ∃ v ∈ d, v.1 = localIdx i ∧ (decodeMark (v.2 c)).super = s ∧ (decodeMark (v.2 c)).child j = a ∧
      chainTop - chainNeed (v.2 c) j ch ≤ pos.val

/-- The pair was never signed in the log. -/
def Unsigned (L : QueryLog SigningSpec) (p : Pair) : Prop :=
  ∀ entry ∈ L, ∀ sig, entry.2 = some sig → ¬(entry.1 = p.1 ∧ sig.randomness = p.2)

variable (b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The excess of the price over the baseline. -/
noncomputable def excess (D : Multiset View) : ℝ≥0∞ := price D - b0

/-- Share of kept views at failing indices. -/
noncomputable def failMass : ℝ≥0∞ :=
  freshAvg Finset.univ fun v : View => if v.1 ∈ Fail then 1 else 0

/-- The cover indicator of a target as a value. -/
noncomputable def witnessFn (v : View) (D : Multiset View) : ℝ≥0∞ := witness v D

/-- Views of a list of pairs. -/
noncomputable def items (s : State) (P : List Pair) : List View := P.map (pview parameter data s)

end Defs

/-! ### The law of a fresh pair -/

section Mean

theorem landing_le_one : landing ≤ 1 := ForestPrice.landing_le_one

/-- **Mean over a fresh pair.** -/
theorem pair_mean (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then F (viewOf u0) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C := by
  have hsplit : ∀ u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then F (viewOf u0) else C) =
      Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then F (viewOf u0) else 0) +
      C * (Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] * (if Landed parameter (blockIndex u0) then 0 else 1)) := by
    intro u0
    split_ifs <;> ring
  simp only [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [fresh_view_mean parameter F, unlanded_mass parameter, mul_comm C]

omit [Params] in
/-- Expectations distribute over a list sum. -/
theorem tsum_list_sum {β γ : Type} (w : β → ℝ≥0∞) (l : List γ) (f : β → γ → ℝ≥0∞) :
    ∑' x, w x * (l.map (f x)).sum = (l.map fun c => ∑' x, w x * f x c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

end Mean

/-! ### Expectation over the block of a fresh pair -/

section PairE

/-- Expectation over a fresh block. -/
noncomputable def pairE (F : HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] * F u0

omit [Params] in
theorem pairE_add (F G : HashOutput → ℝ≥0∞) : pairE (fun a => F a + G a) = pairE F + pairE G := by
  simp only [pairE, mul_add, ENNReal.tsum_add]

omit [Params] in
theorem pairE_mono {F G : HashOutput → ℝ≥0∞} (h : ∀ a, F a ≤ G a) : pairE F ≤ pairE G :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _

omit [Params] in
theorem pairE_const (c : ℝ≥0∞) : pairE (fun _ => c) = c := by
  simp only [pairE, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

omit [Params] in
theorem pairE_const_mul (c : ℝ≥0∞) (F : HashOutput → ℝ≥0∞) : pairE (fun a => c * F a) = c * pairE F := by
  simp only [pairE, mul_left_comm _ c, ENNReal.tsum_mul_left]

omit [Params] in
theorem pairE_list_sum {γ : Type} (l : List γ) (F : HashOutput → γ → ℝ≥0∞) :
    pairE (fun a => (l.map (F a)).sum) = (l.map fun c => pairE fun a => F a c).sum := by
  induction l with
  | nil => simpa using pairE_const 0
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [pairE_add, ih]

theorem pairE_landed (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    pairE (fun u0 => if Landed parameter (blockIndex u0) then F (viewOf u0) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C :=
  pair_mean parameter F C

end PairE

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData)

/-- The block of a new pair stored. -/
noncomputable def withPair (s : State) (p : Pair) (u0 : HashOutput) : State :=
  s.store (pblk parameter data p) u0

/-- The items after a new pair. -/
noncomputable def addPair (P : List Pair) (p : Pair) (u0 : HashOutput) : List Pair :=
  if Landed parameter (blockIndex u0) then p :: P else P

variable {parameter data}

omit [Params] in
theorem withPair_other (s : State) (p : Pair) (u0 : HashOutput) (x : HashInput) (h0 : x ≠ pblk parameter data p) :
    (withPair parameter data s p u0).cache x = s.cache x := by
  unfold withPair
  rw [store_cache_ne _ _ _ h0]

omit [Params] in
theorem withPair_self (s : State) (p : Pair) (u0 : HashOutput) :
    (withPair parameter data s p u0).cache (pblk parameter data p) = some u0 := by
  unfold withPair
  simp [DebtState.store]

omit [Params] in
theorem withPair_other_pair (s : State) (p q : Pair) (hq : q ≠ p) (u0 : HashOutput) :
    (withPair parameter data s p u0).cache (pblk parameter data q) = s.cache (pblk parameter data q) :=
  withPair_other s p u0 _ (pblk_ne_of_ne parameter data hq)

theorem pview_withPair_self (s : State) (p : Pair) (u0 : HashOutput) :
    pview parameter data (withPair parameter data s p u0) p = viewOf u0 := by
  simp only [pview, withPair_self, Option.elim]

theorem pview_withPair_other (s : State) (p q : Pair) (hq : q ≠ p) (u0 : HashOutput) :
    pview parameter data (withPair parameter data s p u0) q = pview parameter data s q := by
  simp only [pview, withPair_other_pair s p q hq]

theorem items_withPair (s : State) (p : Pair) (u0 : HashOutput) (l : List Pair) (hl : p ∉ l) :
    items parameter data (withPair parameter data s p u0) l = items parameter data s l := by
  unfold items
  refine List.map_congr_left fun q hq => ?_
  exact pview_withPair_other s p q (fun h => hl (h ▸ hq)) u0

theorem not_mem_of_fresh {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) : p ∉ P := by
  intro hp
  obtain ⟨u, hu, _⟩ := (hP.mem p).1 hp
  rw [hp0] at hu
  cases hu

theorem pinv_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (u0 : HashOutput) :
    PInv parameter data (withPair parameter data s p u0) (addPair parameter P p u0) := by
  have hpP := not_mem_of_fresh hP hp0
  have hland : ∀ q, q ≠ p → (LandedIn parameter data (withPair parameter data s p u0) q ↔
      LandedIn parameter data s q) := by
    intro q hq
    simp only [LandedIn, withPair_other_pair s p q hq]
  refine ⟨?_, fun q => ?_⟩
  · unfold addPair
    split_ifs
    · exact List.nodup_cons.2 ⟨hpP, hP.nodup⟩
    · exact hP.nodup
  · by_cases hqp : q = p
    · subst hqp
      unfold addPair
      constructor
      · intro hmem
        split_ifs at hmem with hl
        · exact ⟨u0, withPair_self s q u0, hl⟩
        · exact absurd hmem hpP
      · rintro ⟨u, hu, hl⟩
        rw [withPair_self] at hu
        cases hu
        rw [if_pos hl]
        exact List.mem_cons_self ..
    · rw [hland q hqp, ← hP.mem q]
      unfold addPair
      split_ifs
      · simp [hqp]
      · rfl

end NewPair

/-! ### Properties of the forecast bases -/

section NewPairCore

theorem excess_monoP (b0 : ℝ≥0∞) : Monotone' (excess b0) := excess_mono price_mono b0

theorem excess_ne_top (b0 : ℝ≥0∞) (D : Multiset View) : excess b0 D ≠ ⊤ :=
  ne_top_of_le_ne_top (price_ne_top D) tsub_le_self

theorem witnessFn_mono (v : View) : Monotone' (witnessFn v) := witness_mono v

theorem witnessFn_ne_top (v : View) (D : Multiset View) : witnessFn v D ≠ ⊤ := witness_ne_top v D

end NewPairCore

/-! ### Order and congruence -/

section Order

variable {parameter : PublicParameter} {data : PublicData}

theorem items_congr {s s' : State} {l : List Pair} (h : ∀ q ∈ l, pview parameter data s' q = pview parameter data s q) :
    items parameter data s' l = items parameter data s l :=
  List.map_congr_left h

end Order

/-! ### Counting cached randomizers -/

section Count

variable {parameter : PublicParameter} {data : PublicData}

omit [Params] in
theorem blk_injective' (m : Message) : Function.Injective fun ρ : Randomness => blk parameter data m ρ := by
  intro ρ ρ' h
  by_contra hne
  exact blk_ne_of_ne parameter data m hne h

variable (parameter data) in
/-- Digest inputs of a message. -/
noncomputable def zeroInputs (m : Message) : Finset HashInput :=
  Finset.univ.image fun ρ => blk parameter data m ρ

omit [Params] in
theorem cachedCount_eq (m : Message) (s : State) :
    cachedCount parameter data m s = ((zeroInputs parameter data m).filter fun x => s.cache x ≠ none).card := by
  unfold cachedCount zeroInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (blk_injective' m)]

omit [Params] in
theorem count_withPair (m : Message) (s : State) (p : Pair) (u0 : HashOutput) :
    cachedCount parameter data m (withPair parameter data s p u0) ≤ cachedCount parameter data m s + 1 := by
  rw [cachedCount_eq, cachedCount_eq]
  unfold withPair
  exact card_filter_store_le _ _ _ _

end Count

/-! ### The final value and the count invariant -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a forest cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForestCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- Cached digest entries of every message, plus the remaining budget, stay bounded. -/
def CountInv (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, cachedCount parameter data m s + budget ≤ Qtot

end Good

/-! ### One ordinary query -/

section Ordinary

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem readOutside_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (readOutside x s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  rcases readOutside_support x s r hr with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact store_cache_ne s x y hy r.1

omit [Params] in
/-- An ordinary query changes the cache at most at its input. -/
theorem ordinaryStep_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  unfold ordinaryStep at hr
  split at hr
  · exact readOutside_cache_ne x s r hr y hy
  · split at hr
    · exact readOutside_cache_ne x _ r hr y hy
    · split at hr
      · rw [support_map] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rw [sampleCoordinate_expose _ s r' hr']
        rfl
      · exact readOutside_cache_ne x s r hr y hy

omit [Params] in
theorem ordinaryStep_extends (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), Extends s r.2 := by
  intro r hr
  exact extends_costStep model (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)

theorem forestCover_mono (parameter : PublicParameter) (root : Digest) (outcome : HiddenBridge.Outcome)
    (reveals : List Coordinate) {c c' : QueryCache HashSpec} (h : ∀ x v, c x = some v → c' x = some v)
    (hc : HiddenBridge.ForestCover parameter root outcome reveals c) :
    HiddenBridge.ForestCover parameter root outcome reveals c' := by
  obtain ⟨hvalid, digest, hdig, hrest⟩ := hc
  refine ⟨hvalid, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases h0 : c (tweakableHashInput parameter .message
      (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
  | none => rw [h0] at hdig; cases hdig
  | some a =>
      rw [h0] at hdig
      rw [h _ _ h0]
      exact hdig

variable (parameter : PublicParameter) (data : PublicData)

theorem finalValue_presample (y : HashInput) (hk : tg.kind y = .none) (R : List Coordinate)
    (out : Run HashInput Coordinate HiddenBridge.Outcome × State) (s' : State)
    (hs' : s' ∈ support (presample y out.2)) :
    finalValue parameter data tg initial R out ≤ finalValue parameter data tg initial R (out.1, s') := by
  have hreal := realized_presample tg initial y hk out.2 s' hs'
  have hgrow : ∀ x v, out.2.cache x = some v → s'.cache x = some v := by
    cases hc : out.2.cache y with
    | some v =>
        rw [presample_cached y out.2 v hc, support_pure, Set.mem_singleton_iff] at hs'
        rw [hs']
        exact fun _ _ h => h
    | none =>
        rw [presample_fresh y out.2 hc, support_map] at hs'
        obtain ⟨u, _, rfl⟩ := hs'
        exact (extends_store out.2 y u hc).1
  unfold finalValue
  cases out.1.1 with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨forestCover_mono parameter data.root outcome _ hgrow h1.1, fun h => h1.2 (hreal.1 h)⟩ h2
      · exact bot_le
      · exact le_rfl

theorem finalValue_abort (R : List Coordinate) (s : State) :
    finalValue parameter data tg initial R ((none, [], [], []), s) = 0 := rfl

omit [Params] in
theorem interp_mass {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (s : State) :
    ∑' out, Pr[= out | interp tg initial model computation budget s] = 1 :=
  tsum_probOutput_eq_one' probFailure_eq_zero

theorem finalValue_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr[= out | interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s] *
        finalValue parameter data tg initial R out =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ∑' out, Pr[= out | interp tg initial model (next r.1) (budget - 1) r.2] *
          finalValue parameter data tg initial R out := by
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  rfl

omit [Params] in
theorem flagged_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    expectedFlagged tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      (pays tg initial s (.inl (.inr (.inl x))) : ℝ≥0∞) +
        ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          expectedFlagged tg initial model (next r.1) (budget - 1) r.2 := by
  unfold expectedFlagged
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, flaggedCount_append, flaggedCount_touch, Nat.cast_add, mul_add,
    ENNReal.tsum_add, ENNReal.tsum_mul_right, interp_mass]
  rw [one_mul, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

/-- Without a new pair, an ordinary query keeps the items and their views. -/
theorem same_items {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ p, x = pblk parameter data p ∧ s.cache (pblk parameter data p) = none)
    {P : List Pair} (hP : PInv parameter data s P) :
    PInv parameter data s' P ∧ ∀ q ∈ P, pview parameter data s' q = pview parameter data s q := by
  have hkeep : ∀ y, s.cache y ≠ none → s'.cache y = s.cache y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy
    rw [hv]; exact hext.1 y v hv
  have hzero : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q) := by
    intro q
    by_cases hx : x = pblk parameter data q
    · by_cases hn : s.cache (pblk parameter data q) = none
      · exact absurd ⟨q, hx, hn⟩ hnot
      · exact hkeep _ hn
    · exact hother _ (Ne.symm hx)
  have hland : ∀ q, LandedIn parameter data s' q ↔ LandedIn parameter data s q := by
    intro q; simp only [LandedIn, hzero q]
  refine ⟨⟨hP.nodup, fun q => (hP.mem q).trans (hland q).symm⟩, fun q _ => ?_⟩
  unfold pview
  rw [hzero q]

end Ordinary

omit [Params] in
theorem tsum_swap2 {α : Type} (w : α → ℝ≥0∞) (C : α → α → ℝ≥0∞) :
    ∑' u, w u * ∑' u', w u' * C u' u = ∑' a, w a * ∑' b, w b * C a b := by
  calc ∑' u, w u * ∑' u', w u' * C u' u = ∑' u, ∑' u', w u' * (w u * C u' u) :=
        tsum_congr fun u => by rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun u' => mul_left_comm _ _ _
    _ = ∑' u', ∑' u, w u' * (w u * C u' u) := ENNReal.tsum_comm
    _ = _ := tsum_congr fun u' => ENNReal.tsum_mul_left

/-! ### Covers and witnesses -/

/-- A view covered by the reveals is covered by disclosed views accounting for the reveals. -/
theorem witness_pos_of_covered {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (hcov : Covered (HiddenBridge.revealedSet R) (fullDigestView digest)) :
    1 ≤ witness (Lifetime.localDigestView digest) d := by
  have hall : CoverAll (Lifetime.localDigestView digest) d := by
    intro c j i
    rcases hcov c j i with hz | ⟨p, hp, hle⟩
    · exact Or.inl hz
    · simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨v, hv, h1, h2, h3, h4⟩ := hD _ _ _ _ _ _ _ hp
      refine Or.inr ⟨v, hv, by rw [localDigestView_fst]; exact h1, ?_⟩
      refine ⟨by rw [h2]; rfl, by rw [h3]; rfl, ?_⟩
      have hneed : chainNeed (coordField digest c) j i ≤ chainTop := by
        have := (lut ((decodeMark (coordField digest c)).word j) i).isLt
        simp only [chainNeed, chainTop] at this ⊢
        omega
      have hneedv : chainNeed (v.2 c) j i ≤ chainTop := by
        have := (lut ((decodeMark (v.2 c)).word j) i).isLt
        simp only [chainNeed, chainTop] at this ⊢
        omega
      simp only [fullDigestView] at hle
      change chainNeed (coordField digest c) j i ≤ chainNeed (v.2 c) j i
      omega
  unfold witness
  rw [if_pos hall]

/-! ### What a signing call adds -/

/-- The pairs that are not excluded. -/
noncomputable def others (excl : Pair → Prop) (P : List Pair) : List Pair := P.filter fun q => ¬excl q

omit [Params] in
theorem mem_others {excl : Pair → Prop} {P : List Pair} {q : Pair} : q ∈ others excl P ↔ q ∈ P ∧ ¬excl q := by
  unfold others; simp

omit [Params] in
theorem others_nodup {excl : Pair → Prop} {P : List Pair} (h : P.Nodup) : (others excl P).Nodup := h.filter _

section SignDefs

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- Randomizers of the message whose block is new and lands. -/
noncomputable def newRand (s' : State) : Finset Randomness :=
  Finset.univ.filter fun ρ => s.cache (blk parameter data m ρ) = none ∧ LandedIn parameter data s' (m, ρ)

/-- Pairs created by a signing call. -/
noncomputable def newPairs (s' : State) : List Pair := (newRand parameter data m s s').toList.map fun ρ => (m, ρ)

/-- Disclosure of an existing pair signed by the call. -/
noncomputable def poolDisc (out : Run HashInput Coordinate (Option Signature) × State) : Multiset View :=
  out.1.1.elim 0 fun r => r.elim 0 fun sig =>
    if s.cache (blk parameter data m sig.randomness) = none then 0
    else {pview parameter data out.2 (m, sig.randomness)}

/-- Disclosures after a signing call. -/
noncomputable def discAfter (d : Multiset View) (out : Run HashInput Coordinate (Option Signature) × State) :
    Multiset View :=
  d + ((newPairs parameter data m s out.2).map (pview parameter data out.2) : Multiset View) +
    poolDisc parameter data m s out

theorem newPairs_nodup (s' : State) : (newPairs parameter data m s s').Nodup :=
  (Finset.nodup_toList _).map fun _ _ h => (Prod.ext_iff.1 h).2

theorem mem_newPairs {s' : State} {q : Pair} :
    q ∈ newPairs parameter data m s s' ↔ q.1 = m ∧ s.cache (pblk parameter data q) = none ∧
      LandedIn parameter data s' q := by
  unfold newPairs newRand
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, ⟨h0, hl⟩, rfl⟩
    exact ⟨rfl, h0, hl⟩
  · rintro ⟨hm, h0, hl⟩
    exact ⟨q.2, ⟨by rw [← hm]; exact h0, by rw [← hm]; exact hl⟩, by rw [← hm]⟩

end SignDefs

/-! ### The three shapes of a completed signing call -/

section SignShape

variable (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) {s : State}

theorem newRand_eq_empty {s' : State} (h : ∀ ρ, RelatedAt parameter data m s s' ρ) :
    newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ hρ => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  obtain ⟨h0, u, hu, hl⟩ := hρ
  rcases h ρ with he | ⟨_, u', hu', hnl⟩
  · change s'.cache (blk parameter data m ρ) = some u at hu
    rw [he, h0] at hu; cases hu
  · change s'.cache (blk parameter data m ρ) = some u at hu
    rw [hu'] at hu; cases hu; exact hnl hl

theorem newRand_eq_single {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ) = none) (hl : LandedIn parameter data s' (m, ρ)) :
    newRand parameter data m s s' = {ρ} := by
  ext ρ'
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0', u, hu, hl'⟩
    by_contra hne
    rcases h ρ' hne with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ') = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ') = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'
  · rintro rfl
    exact ⟨h0, hl⟩

theorem newRand_eq_empty_of_pool {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ) ≠ none) : newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ' hρ' => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ'
  obtain ⟨h0', u, hu, hl'⟩ := hρ'
  by_cases hne : ρ' = ρ
  · subst hne; exact h0 h0'
  · rcases h ρ' hne with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ') = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ') = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'

/-- **Shapes.** A completed signing call adds nothing, one fresh landed pair, or signs a cached
landed pair. -/
theorem sign_shape {reveals : List Coordinate} {r : Option Signature} {s' : State}
    (post : SignPost parameter data m Fail s s' reveals r)
    (out : Run HashInput Coordinate (Option Signature) × State) (hout2 : out.2 = s') (hres : out.1.1 = some r) :
    (newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = 0) ∨
    (∃ ρ u0, newRand parameter data m s s' = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
      s'.cache (blk parameter data m ρ) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s.cache (blk parameter data m ρ) = none ∧
      (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ') ∧
      (r = none → (viewOf u0).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
    (∃ ρ u0 sig, newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = {viewOf u0} ∧
      r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ) = some u0 ∧
      s'.cache (blk parameter data m ρ) = some u0) := by
  subst hout2
  rcases post with ⟨hrn, _, hrel⟩ | ⟨ρ, u0, ⟨hs0, hl, hs0r, hothers⟩, _, hsig, hfl⟩
  · left
    refine ⟨newRand_eq_empty parameter data m hrel, ?_⟩
    unfold poolDisc; rw [hres, hrn]; rfl
  · rcases hs0r with hn | he
    · right; left
      refine ⟨ρ, u0, newRand_eq_single parameter data m hothers hn ⟨u0, hs0, hl⟩, ?_, hs0, hl, hn,
        hothers, fun hrn => (hfl hrn).2 hn, hsig⟩
      unfold poolDisc
      rw [hres]
      rcases r with _ | sig
      · rfl
      · simp only [Option.elim]
        rw [hsig sig rfl, if_pos hn]
    · rcases r with _ | sig
      · left
        refine ⟨newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _), ?_⟩
        unfold poolDisc; rw [hres]; rfl
      · right; right
        refine ⟨ρ, u0, sig, newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _),
          ?_, rfl, hsig sig rfl, he, hs0⟩
        unfold poolDisc
        rw [hres]
        simp only [Option.elim]
        rw [hsig sig rfl, if_neg (by rw [he]; exact Option.some_ne_none _)]
        congr 1
        simp only [pview]
        change (out.2.cache (blk parameter data m ρ)).elim _ viewOf = _
        rw [hs0]
        rfl

end SignShape

/-! ### Cached pairs -/

section SignParams

variable {parameter : PublicParameter} {data : PublicData} {m : Message}

theorem related_self (s : State) : Related parameter data m s s := fun _ => Or.inl rfl

theorem pview_of_cached {s' : State} {q : Pair} {u0 : HashOutput} (h0 : s'.cache (pblk parameter data q) = some u0) :
    pview parameter data s' q = viewOf u0 := by
  simp only [pview, h0, Option.elim]

theorem landed_of_cached {s : State} {P : List Pair} (hP : PInv parameter data s P) {q : Pair}
    (hq : q ∈ P) : ∃ u0, s.cache (pblk parameter data q) = some u0 ∧ Landed parameter (blockIndex u0) :=
  (hP.mem q).1 hq

end SignParams

/-! ### Signing helpers -/

omit [Params] in
theorem erase_eq_filter' {P : List Pair} (hP : P.Nodup) (q : Pair) : P.erase q = others (· = q) P := by
  rw [hP.erase_eq_filter]
  unfold others
  congr 1
  funext q'
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne]

omit [Params] in
theorem filter_false' (P : List Pair) : others (fun _ => False) P = P := by unfold others; simp

omit [Params] in
theorem unsigned_of_append {L : QueryLog SigningSpec} {e : (_ : Message) × Option Signature} {q : Pair}
    (h : Unsigned (L ++ [e]) q) : Unsigned L q :=
  fun entry he sig hs => h entry (List.mem_append_left _ he) sig hs

omit [Params] in
theorem not_unsigned_signed {m : Message} {L : QueryLog SigningSpec} {sig : Signature} :
    ¬Unsigned (L ++ [⟨m, some sig⟩]) (m, sig.randomness) := fun h =>
  h ⟨m, some sig⟩ (List.mem_append_right _ (List.mem_singleton_self _)) sig rfl ⟨rfl, rfl⟩

section SignGood

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem interpThen_some {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

omit [Params] in
theorem interpThen_none {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

end SignGood

end Sphincs.Security.ForsPotential
