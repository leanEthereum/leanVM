import FORS.ScanSigner.AfterSigning
import FORS.CoverPotential.Presample
import FORS.Base.VirtualMono
import FORS.Classification.Win

/-! Ingredients of the FORS potential of the lazy run. Every cached landed message-randomizer pair
is an item; the unsigned ones are candidates. A pair owns one digest block per call
(`digestCalls` of them): the block of `firstCall` carries the index and alone decides landing,
while the kept view needs them all. This file defines the pairs, their views, the item and
disclosure invariants, the final value (a FORS cover) and proves the facts about fresh pairs,
ordinary queries and signing calls that the one-coin potentials of `CoverPotential/OneCoin` and
`CoverPotential/GenericWitness` build on. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A message and a randomizer. -/
abbrev Pair := Message × Randomness

abbrev State := DebtState HashInput HashOutput Coordinate

noncomputable instance viewInhabited : Inhabited View := ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩

theorem payload_pair_injective (root : Digest) {m m' : Message} {ρ ρ' : Randomness}
    (h : messageDigestPayload root m ρ = messageDigestPayload root m' ρ') : m = m' ∧ ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparts.1, bytesLE_injective hparts.2⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- The digest block of one call of a pair. -/
abbrev pblk (p : Pair) (call : DigestCall) : HashInput := GraphView.pblk parameter data p.1 p.2 call

/-- The calls of one pair query distinct blocks (`GraphView.pblk_injective`). -/
theorem pblk_call_injective (p : Pair) : Function.Injective (pblk parameter data p) :=
  GraphView.pblk_injective parameter data p.1 p.2

theorem pblk_injective {p q : Pair} {call call' : DigestCall}
    (h : pblk parameter data p call = pblk parameter data q call') : p = q ∧ call = call' := by
  obtain ⟨hfields, -, hpayload⟩ := tweakableInput_injective h
  obtain ⟨hm, hρ⟩ := payload_pair_injective data.root hpayload
  refine ⟨Prod.ext hm hρ, ?_⟩
  simpa using hashFields_injective (left := .message call) (right := .message call') trivial trivial hfields

theorem pblk_ne_of_ne {p q : Pair} (h : p ≠ q) (call call' : DigestCall) :
    pblk parameter data p call ≠ pblk parameter data q call' := fun heq =>
  h (pblk_injective parameter data heq).1

theorem pblk_ne_call {p : Pair} {call call' : DigestCall} (h : call ≠ call') :
    pblk parameter data p call ≠ pblk parameter data p call' := fun heq =>
  h (pblk_injective parameter data heq).2

/-- The blocks of a pair, read through `GraphView.pcache`, when every call is cached. -/
theorem pcache_of_cached {s : State} {p : Pair} {u : DigestCall → HashOutput}
    (h : ∀ call, s.cache (pblk parameter data p call) = some (u call)) :
    pcache parameter data p.1 s p.2 = some u :=
  allSome_of_eq _ u h

theorem cached_of_pcache {s : State} {p : Pair} {u : DigestCall → HashOutput}
    (h : pcache parameter data p.1 s p.2 = some u) (call : DigestCall) :
    s.cache (pblk parameter data p call) = some (u call) :=
  HiddenBridge.allSome_some h call

theorem pcache_of_uncached {s : State} {p : Pair} {call : DigestCall}
    (h : s.cache (pblk parameter data p call) = none) : pcache parameter data p.1 s p.2 = none := by
  unfold pcache Completeness.allSome
  exact dif_neg fun hall => by simpa [h] using hall call

theorem first_of_pcache {s : State} {mes : Message} {ρ : Randomness} {u : DigestCall → HashOutput}
    (h : pcache parameter data mes s ρ = some u) : s.cache (blk parameter data mes ρ) = some (u firstCall) :=
  HiddenBridge.allSome_some h firstCall

/-- A value read from the blocks of a pair only grows when a fresh input is stored: either the
blocks are not all cached yet, or the store misses every one of them. -/
theorem pcache_elim_store_mono (mes : Message) (ρ : Randomness) (s : State) (y : HashInput)
    (v : HashOutput) (hy : s.cache y = none) (g : (DigestCall → HashOutput) → ℝ≥0∞) :
    (pcache parameter data mes s ρ).elim 0 g ≤ (pcache parameter data mes (s.store y v) ρ).elim 0 g := by
  cases hc : pcache parameter data mes s ρ with
  | none => exact bot_le
  | some u =>
      have hall := cached_of_pcache (p := (mes, ρ)) parameter data hc
      have hstore : ∀ call, (s.store y v).cache (pblk parameter data (mes, ρ) call) = some (u call) := by
        intro call
        have hne : pblk parameter data (mes, ρ) call ≠ y := by
          intro heq
          have hcall := hall call
          rw [heq, hy] at hcall
          cases hcall
        rw [store_cache_ne s y _ hne v]
        exact hall call
      rw [pcache_of_cached (p := (mes, ρ)) parameter data hstore]

theorem pcache_congr {s s' : State} {p : Pair}
    (h : ∀ call, s'.cache (pblk parameter data p call) = s.cache (pblk parameter data p call)) :
    pcache parameter data p.1 s' p.2 = pcache parameter data p.1 s p.2 :=
  congrArg _ (funext h)

/-- The kept view of a pair whose blocks are all cached. -/
noncomputable def pview (s : State) (p : Pair) : View :=
  (pcache parameter data p.1 s p.2).elim default viewOf

theorem pview_congr {s s' : State} {p : Pair}
    (h : ∀ call, s'.cache (pblk parameter data p call) = s.cache (pblk parameter data p call)) :
    pview parameter data s' p = pview parameter data s p := by
  unfold pview
  rw [pcache_congr parameter data h]

/-- The block of the first call of the pair is cached and lands. -/
def LandedIn (s : State) (p : Pair) : Prop :=
  ∃ u0, s.cache (pblk parameter data p firstCall) = some u0 ∧ Landed parameter (blockIndex u0)

/-- The items are exactly the landed pairs; a landed pair has every block; a pair without its
first block has no block at all. -/
structure PInv (s : State) (P : List Pair) : Prop where
  nodup : P.Nodup
  mem : ∀ p, p ∈ P ↔ LandedIn parameter data s p
  all : ∀ p, LandedIn parameter data s p → ∀ call, s.cache (pblk parameter data p call) ≠ none
  first : ∀ p, s.cache (pblk parameter data p firstCall) = none →
    ∀ call, s.cache (pblk parameter data p call) = none

/-- The local index of a leaf index. -/
def localIdx (i : Index) : Fin (2 ^ subtreeHeight) := ⟨i.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem localDigestView_fst (digest : MessageDigest) :
    (Lifetime.localDigestView digest).1 = localIdx (digestIndex digest) := rfl

theorem localDigestView_snd (digest : MessageDigest) :
    (Lifetime.localDigestView digest).2 = digestLeaves digest := rfl

/-- The disclosed views account for every revealed FORS coordinate: some disclosed view at its
index selects its leaf in its tree. -/
def DInv (R : List Coordinate) (d : Multiset View) : Prop :=
  ∀ i κ l q, Coordinate.fors i κ l q ∈ R → ∃ v ∈ d, v.1 = localIdx i ∧ v.2 κ = l

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

end Defs

/-! ### The law of a fresh pair -/

section Mean

theorem landing_le_one : landing ≤ 1 := ForsPrice.landing_le_one

/-- **Mean over a fresh pair.** Only the block of `firstCall` decides landing. -/
theorem pair_mean (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then F (viewOf u) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C := by
  have hsplit : ∀ u : DigestCall → HashOutput,
      Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then F (viewOf u) else C) =
      Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then F (viewOf u) else 0) +
      C * (Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then 0 else 1)) := by
    intro u
    split_ifs <;> ring
  simp only [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [fresh_view_mean parameter F, unlanded_mass parameter, mul_comm C]

/-- Expectations distribute over a list sum. -/
theorem tsum_list_sum {β γ : Type} (w : β → ℝ≥0∞) (l : List γ) (f : β → γ → ℝ≥0∞) :
    ∑' x, w x * (l.map (f x)).sum = (l.map fun c => ∑' x, w x * f x c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

end Mean

/-! ### Expectation over the blocks of a fresh pair -/

section PairE

/-- Expectation over the fresh blocks of a pair, one per digest call. -/
noncomputable def pairE (F : (DigestCall → HashOutput) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] * F u

theorem pairE_add (F G : (DigestCall → HashOutput) → ℝ≥0∞) :
    pairE (fun a => F a + G a) = pairE F + pairE G := by
  simp only [pairE, mul_add, ENNReal.tsum_add]

theorem pairE_mono {F G : (DigestCall → HashOutput) → ℝ≥0∞} (h : ∀ a, F a ≤ G a) : pairE F ≤ pairE G :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _

theorem pairE_const (c : ℝ≥0∞) : pairE (fun _ => c) = c := by
  simp only [pairE, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

theorem pairE_const_mul (c : ℝ≥0∞) (F : (DigestCall → HashOutput) → ℝ≥0∞) :
    pairE (fun a => c * F a) = c * pairE F := by
  simp only [pairE, mul_left_comm _ c, ENNReal.tsum_mul_left]

theorem pairE_list_sum {γ : Type} (l : List γ) (F : (DigestCall → HashOutput) → γ → ℝ≥0∞) :
    pairE (fun a => (l.map (F a)).sum) = (l.map fun c => pairE fun a => F a c).sum := by
  induction l with
  | nil => simpa using pairE_const 0
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [pairE_add, ih]

theorem pairE_landed (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then F (viewOf u) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C :=
  pair_mean parameter F C

end PairE

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData)

/-- Every block of a new pair stored at once. -/
noncomputable def withPair (s : State) (p : Pair) (u : DigestCall → HashOutput) : State :=
  storeAll (pblk parameter data p) u s

/-- The items after a new pair. -/
noncomputable def addPair (P : List Pair) (p : Pair) (u : DigestCall → HashOutput) : List Pair :=
  if Landed parameter (blockIndex (u firstCall)) then p :: P else P

variable {parameter data}

theorem withPair_other (s : State) (p : Pair) (u : DigestCall → HashOutput) (x : HashInput)
    (h0 : ∀ call, x ≠ pblk parameter data p call) :
    (withPair parameter data s p u).cache x = s.cache x :=
  storeAll_cache_other _ u s x fun call heq => h0 call heq.symm

theorem withPair_self (s : State) (p : Pair) (u : DigestCall → HashOutput) (call : DigestCall) :
    (withPair parameter data s p u).cache (pblk parameter data p call) = some (u call) :=
  storeAll_cache_self _ (pblk_call_injective parameter data p) u s call

theorem withPair_known (s : State) (p : Pair) (u : DigestCall → HashOutput) :
    (withPair parameter data s p u).known = s.known ∧
      (withPair parameter data s p u).guesses = s.guesses :=
  storeAll_known _ u s

theorem withPair_other_pair (s : State) (p q : Pair) (hq : q ≠ p) (u : DigestCall → HashOutput)
    (call : DigestCall) :
    (withPair parameter data s p u).cache (pblk parameter data q call) =
      s.cache (pblk parameter data q call) :=
  withPair_other s p u _ fun call' => pblk_ne_of_ne parameter data hq call call'

theorem pview_withPair_self (s : State) (p : Pair) (u : DigestCall → HashOutput) :
    pview parameter data (withPair parameter data s p u) p = viewOf u := by
  simp only [pview, pcache_of_cached parameter data (withPair_self s p u), Option.elim]

theorem pview_withPair_other (s : State) (p q : Pair) (hq : q ≠ p) (u : DigestCall → HashOutput) :
    pview parameter data (withPair parameter data s p u) q = pview parameter data s q := by
  simp only [pview, pcache_congr parameter data (withPair_other_pair s p q hq u)]

theorem not_mem_of_fresh {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) : p ∉ P := by
  intro hp
  obtain ⟨u, hu, _⟩ := (hP.mem p).1 hp
  rw [hp0] at hu
  cases hu

/-- Storing a new pair only grows the state: by `PInv.first` none of its blocks was cached. -/
theorem extends_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (u : DigestCall → HashOutput) :
    Extends s (withPair parameter data s p u) := by
  obtain ⟨hk, hg⟩ := withPair_known (parameter := parameter) (data := data) s p u
  refine ⟨fun x v hx => ?_, fun c v hc => by rw [hk]; exact hc, fun g hg' => by rw [hg]; exact hg'⟩
  by_cases hcall : ∃ call, x = pblk parameter data p call
  · obtain ⟨call, rfl⟩ := hcall
    rw [hP.first p hp0 call] at hx
    cases hx
  · push Not at hcall
    rw [withPair_other s p u x hcall]
    exact hx

theorem pinv_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (u : DigestCall → HashOutput) :
    PInv parameter data (withPair parameter data s p u) (addPair parameter P p u) := by
  have hpP := not_mem_of_fresh hP hp0
  have hland : ∀ q, q ≠ p → (LandedIn parameter data (withPair parameter data s p u) q ↔
      LandedIn parameter data s q) := by
    intro q hq
    simp only [LandedIn, withPair_other_pair s p q hq]
  refine ⟨?_, fun q => ?_, fun q hq call => ?_, fun q hq call => ?_⟩
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
        · exact ⟨u firstCall, withPair_self s q u firstCall, hl⟩
        · exact absurd hmem hpP
      · rintro ⟨u0, hu, hl⟩
        rw [withPair_self s q u firstCall] at hu
        cases hu
        rw [if_pos hl]
        exact List.mem_cons_self ..
    · rw [hland q hqp, ← hP.mem q]
      unfold addPair
      split_ifs
      · simp [hqp]
      · rfl
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_self s q u call]
      exact Option.some_ne_none _
    · rw [withPair_other_pair s p q hqp]
      exact hP.all q ((hland q hqp).1 hq) call
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_self s q u firstCall] at hq
      cases hq
    · rw [withPair_other_pair s p q hqp] at hq ⊢
      exact hP.first q hq call

end NewPair

/-! ### Properties of the forecast bases -/

section NewPairCore

theorem excess_monoP (b0 : ℝ≥0∞) : Monotone' (excess b0) := excess_mono price_mono b0

theorem excess_ne_top (b0 : ℝ≥0∞) (D : Multiset View) : excess b0 D ≠ ⊤ :=
  ne_top_of_le_ne_top (price_ne_top D) tsub_le_self

theorem witnessFn_mono (v : View) : Monotone' (witnessFn v) := witness_mono v

theorem witnessFn_ne_top (v : View) (D : Multiset View) : witnessFn v D ≠ ⊤ := witness_ne_top v D

end NewPairCore

/-! ### Counting cached randomizers -/

section Count

variable {parameter : PublicParameter} {data : PublicData}

theorem blk_injective' (m : Message) : Function.Injective fun ρ : Randomness => blk parameter data m ρ := by
  intro ρ ρ' h
  by_contra hne
  exact blk_ne_of_ne parameter data m hne h

variable (parameter data) in
/-- Digest inputs of the first call of a message. -/
noncomputable def zeroInputs (m : Message) : Finset HashInput :=
  Finset.univ.image fun ρ => blk parameter data m ρ

theorem cachedCount_eq (m : Message) (s : State) :
    cachedCount parameter data m s = ((zeroInputs parameter data m).filter fun x => s.cache x ≠ none).card := by
  unfold cachedCount zeroInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (blk_injective' m)]

/-- A state that differs at one input only has at most one more cached entry of a set. -/
theorem card_filter_le_of_off (T : Finset HashInput) (s s' : State) (x : HashInput)
    (h : ∀ y ∈ T, y ≠ x → s'.cache y = s.cache y) :
    (T.filter fun y => s'.cache y ≠ none).card ≤ (T.filter fun y => s.cache y ≠ none).card + 1 := by
  have hsub : (T.filter fun y => s'.cache y ≠ none) ⊆
      insert x (T.filter fun y => s.cache y ≠ none) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_cases hyx : y = x
    · rw [hyx]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy.1, by rw [← h y hy.1 hyx]; exact hy.2⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

theorem count_withPair (m : Message) (s : State) (p : Pair) (u : DigestCall → HashOutput) :
    cachedCount parameter data m (withPair parameter data s p u) ≤ cachedCount parameter data m s + 1 := by
  rw [cachedCount_eq, cachedCount_eq]
  refine card_filter_le_of_off _ s _ (pblk parameter data p firstCall) fun y hy hyx => ?_
  obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.1 hy
  refine withPair_other s p u _ fun call heq => hyx ?_
  obtain ⟨-, hcall⟩ := pblk_injective parameter data
    (show pblk parameter data (m, ρ) firstCall = pblk parameter data p call from heq)
  rw [hcall]
  exact heq

end Count

/-! ### The final value and the count invariant -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a FORS cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForsCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- Cached digest entries of every message, plus the remaining budget, stay bounded. -/
def CountInv (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, cachedCount parameter data m s + budget ≤ Qtot

end Good

/-! ### One ordinary query -/

section Ordinary

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem readOutside_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (readOutside x s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  rcases readOutside_support x s r hr with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact store_cache_ne s x y hy r.1

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

theorem ordinaryStep_extends (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), Extends s r.2 := by
  intro r hr
  exact extends_costStep model (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)

variable (parameter : PublicParameter) (data : PublicData)

theorem finalValue_abort (R : List Coordinate) (s : State) :
    finalValue parameter data tg initial R ((none, [], [], []), s) = 0 := rfl

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

/-- Without a new pair, an ordinary query keeps the items and their views. A query of a later call
of a pair whose first block is cached changes no item: landing reads the first block alone. -/
theorem same_items {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none)
    {P : List Pair} (hP : PInv parameter data s P) :
    PInv parameter data s' P ∧ ∀ q ∈ P, pview parameter data s' q = pview parameter data s q := by
  have hkeep : ∀ y, s.cache y ≠ none → s'.cache y = s.cache y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy
    rw [hv]; exact hext.1 y v hv
  have hfirst : ∀ q : Pair, s'.cache (pblk parameter data q firstCall) =
      s.cache (pblk parameter data q firstCall) := by
    intro q
    by_cases hx : x = pblk parameter data q firstCall
    · by_cases hn : s.cache (pblk parameter data q firstCall) = none
      · exact absurd ⟨q, firstCall, hx, hn⟩ hnot
      · exact hkeep _ hn
    · exact hother _ (Ne.symm hx)
  have hland : ∀ q, LandedIn parameter data s' q ↔ LandedIn parameter data s q := by
    intro q; simp only [LandedIn, hfirst q]
  have hcached : ∀ q : Pair, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
    fun q hq call => hkeep _ (hP.all q hq call)
  refine ⟨⟨hP.nodup, fun q => (hP.mem q).trans (hland q).symm, fun q hq call => ?_, fun q hq call => ?_⟩,
    fun q hq => ?_⟩
  · rw [hcached q ((hland q).1 hq) call]
    exact hP.all q ((hland q).1 hq) call
  · rw [hfirst q] at hq
    by_cases hxc : x = pblk parameter data q call
    · exact absurd ⟨q, call, hxc, hq⟩ hnot
    · rw [hother _ (Ne.symm hxc)]
      exact hP.first q hq call
  · unfold pview
    rw [pcache_congr parameter data (hcached q ((hP.mem q).1 hq))]

end Ordinary

/-! ### Covers and witnesses -/

/-- A view covered by the reveals is covered by disclosed views accounting for the reveals. -/
theorem witness_pos_of_covered {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (hcov : Covered (HiddenBridge.revealedSet R) (fullDigestView digest)) :
    1 ≤ witness (Lifetime.localDigestView digest) d := by
  have hall : CoverAll (Lifetime.localDigestView digest) d := by
    intro κ
    have hκ := hcov κ
    unfold TreeCov at hκ
    simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hκ
    obtain ⟨v, hv, h1, h2⟩ := hD _ _ _ _ hκ
    exact ⟨v, hv, by rw [localDigestView_fst]; exact h1, by rw [localDigestView_snd]; exact h2⟩
  unfold witness
  rw [if_pos hall]

/-! ### Presampling the other calls of a pair -/

section PresampleFamily

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- `HiddenDebt.interp_presample_fresh_le` with the growth hypothesis only at the presampled
input: the final value of the run is not monotone under a store at a *targeted* input. -/
theorem interp_presample_fresh_leF (x : HashInput) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp CostSpec α) (budget : ℕ) (state : State) (hx : state.cache x = none)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞)
    (hF : ∀ out (v : HashOutput), out.2.cache x = none → F out ≤ F (out.1, out.2.store x v)) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * F out ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model
        computation budget (state.store x v)] * F out := by
  refine le_trans (interp_presample_le tg initial model x hk computation budget state F fun out s hs => ?_) ?_
  · cases hc : out.2.cache x with
    | some w =>
        rw [presample_cached x out.2 w hc, support_pure, Set.mem_singleton_iff] at hs
        rw [hs]
    | none =>
        rw [presample_fresh x out.2 hc, support_map] at hs
        obtain ⟨v, _, rfl⟩ := hs
        exact hF out v hc
  · rw [presample_fresh x state hx, tsum_probOutput_map_mul, tsum_uniform_eq]

set_option maxRecDepth 100000 in
/-- `HiddenDebt.interp_presampleAll_le` with the growth hypothesis only at the family. -/
theorem interp_presampleAll_leF {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞) :
    ∀ {n : ℕ} (x : Fin n → HashInput), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      (∀ out (i : Fin n) (v : HashOutput), out.2.cache (x i) = none →
        F out ≤ F (out.1, out.2.store (x i) v)) →
      ∀ state : State, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr[= out | interp tg initial model computation budget state] * F out ≤
          ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → HashOutput,
            ∑' out, Pr[= out | interp tg initial model computation budget (storeAll x u state)] * F out
  | 0, _, _, _, _, _, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, hF, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      refine le_trans (interp_presample_fresh_leF tg initial model (x 0) (hk 0) computation budget state
        (hfresh 0) F fun out v hc => hF out 0 v hc) ?_
      have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model computation budget
            (state.store (x 0) v)] * F out ≤
          ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → HashOutput, ∑' out,
            Pr[= out | interp tg initial model computation budget
              (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out := fun v =>
        interp_presampleAll_leF computation budget F (Fin.tail x) hxt (fun i => hk i.succ)
          (fun out i v' hc => hF out i.succ v' hc) _ fun i => by
            show (state.store (x 0) v).cache (x i.succ) = none
            rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
            exact hfresh i.succ
      calc (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model
              computation budget (state.store (x 0) v)] * F out
          ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ *
              ∑ w : Fin n → HashOutput, ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v))] * F out) := by
            gcongr with v
            exact hrest v
        _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → HashOutput,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state)] * F out := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (n + 1))⁻¹ * z) ?_
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => HashOutput) _ _ fun _ => rfl

set_option maxRecDepth 100000 in
/-- **A query of one call of a fresh pair**: `HiddenDebt.interp_presample_new` with the growth
hypothesis only at the family. -/
theorem interp_presample_newF {α : Type} {n : ℕ} (x : Fin n → HashInput) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : HashOutput → OracleComp CostSpec α)
    (budget : ℕ) (state : State) (hfresh : ∀ i, state.cache (x i) = none)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞)
    (hF : ∀ out (i : Fin n) (v : HashOutput), out.2.cache (x i) = none →
      F out ≤ F (out.1, out.2.store (x i) v)) :
    ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * F out ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → HashOutput,
        ∑' out, Pr[= out | interp tg initial model (next (u c)) budget (storeAll x u state)] * F out := by
  obtain ⟨mm, rfl⟩ : ∃ mm, n = mm + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (mm + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (mm + 1) → HashInput := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
        (state.store (x c) v)] * F out ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ mm)⁻¹ * ∑ w : Fin mm → HashOutput, ∑' out,
        Pr[= out | interp tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)] * F out := by
    intro v
    rw [← hx'0]
    exact interp_presampleAll_leF tg initial model (next v) budget F (Fin.tail x') hxt
      (fun i => hk _) (fun out i v' hc => hF out (σ i.succ) v' hc) _ fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
          (state.store (x c) v)] * F out
      ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card HashOutput : ℝ≥0∞) ^ mm)⁻¹ *
          ∑ w : Fin mm → HashOutput, ∑' out, Pr[= out | interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state)] * F out) := by
        gcongr with v
        exact hrest v
    _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * ∑ v, ∑ w : Fin mm → HashOutput,
          ∑' out, Pr[= out | interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state)] * F out := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
    _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * ∑ u' : Fin (mm + 1) → HashOutput,
          ∑' out, Pr[= out | interp tg initial model (next (u' 0)) budget (storeAll x' u' state)] * F out := by
        refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * z) ?_
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => HashOutput) _ _ fun _ => rfl
    _ = _ := by
        refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * z) ?_
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl HashOutput)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl HashOutput)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3

end PresampleFamily

/-! ### What a signing call adds -/

section SignDefs

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- Randomizers of the message whose first block is new and lands. -/
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
    q ∈ newPairs parameter data m s s' ↔ q.1 = m ∧ s.cache (pblk parameter data q firstCall) = none ∧
      LandedIn parameter data s' q := by
  unfold newPairs newRand
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, ⟨h0, hl⟩, rfl⟩
    exact ⟨rfl, h0, hl⟩
  · rintro ⟨hm, h0, hl⟩
    exact ⟨q.2, ⟨by rw [← hm]; exact h0, by rw [← hm]; exact hl⟩, by rw [← hm]⟩

end SignDefs

/-! ### Cached pairs -/

section SignParams

variable {parameter : PublicParameter} {data : PublicData} {m : Message}

theorem pview_of_pcache {s' : State} {q : Pair} {u : DigestCall → HashOutput}
    (h0 : pcache parameter data q.1 s' q.2 = some u) : pview parameter data s' q = viewOf u := by
  simp only [pview, h0, Option.elim]

theorem pview_of_cached {s' : State} {q : Pair} {u : DigestCall → HashOutput}
    (h0 : ∀ call, s'.cache (pblk parameter data q call) = some (u call)) :
    pview parameter data s' q = viewOf u :=
  pview_of_pcache (pcache_of_cached parameter data h0)

theorem landed_of_cached {s : State} {P : List Pair} (hP : PInv parameter data s P) {q : Pair}
    (hq : q ∈ P) : ∃ u0, s.cache (pblk parameter data q firstCall) = some u0 ∧
      Landed parameter (blockIndex u0) :=
  (hP.mem q).1 hq

end SignParams

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
landed pair. The selected pair has every digest call cached. -/
theorem sign_shape {reveals : List Coordinate} {r : Option Signature} {s' : State}
    (post : SignPost parameter data m Fail s s' reveals r)
    (out : Run HashInput Coordinate (Option Signature) × State) (hout2 : out.2 = s') (hres : out.1.1 = some r) :
    (newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = 0) ∨
    (∃ ρ u, newRand parameter data m s s' = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
      pcache parameter data m s' ρ = some u ∧
      Landed parameter (blockIndex (u firstCall)) ∧
      s.cache (blk parameter data m ρ) = none ∧
      (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ') ∧
      (r = none → (viewOf u).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
    (∃ ρ u sig, newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = {viewOf u} ∧
      r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ) = some (u firstCall) ∧
      pcache parameter data m s' ρ = some u) := by
  subst hout2
  rcases post with ⟨hrn, _, hrel⟩ | ⟨ρ, u, ⟨hs0, hl, hs0r, hothers⟩, _, hsig, hfl⟩
  · left
    refine ⟨newRand_eq_empty parameter data m hrel, ?_⟩
    unfold poolDisc; rw [hres, hrn]; rfl
  · rcases hs0r with hn | he
    · right; left
      refine ⟨ρ, u, newRand_eq_single parameter data m hothers hn
          ⟨u firstCall, cached_of_pcache (p := (m, ρ)) parameter data hs0 firstCall, hl⟩, ?_,
        hs0, hl, hn, hothers, fun hrn => (hfl hrn).2 hn, hsig⟩
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
        refine ⟨ρ, u, sig, newRand_eq_empty_of_pool parameter data m hothers
          (by rw [he]; exact Option.some_ne_none _), ?_, rfl, hsig sig rfl, he, hs0⟩
        unfold poolDisc
        rw [hres]
        simp only [Option.elim]
        rw [hsig sig rfl, if_neg (by rw [he]; exact Option.some_ne_none _)]
        congr 1
        exact pview_of_pcache (q := (m, ρ)) hs0

end SignShape

/-! ### Signing helpers -/

theorem unsigned_of_append {L : QueryLog SigningSpec} {e : (_ : Message) × Option Signature} {q : Pair}
    (h : Unsigned (L ++ [e]) q) : Unsigned L q :=
  fun entry he sig hs => h entry (List.mem_append_left _ he) sig hs

theorem not_unsigned_signed {m : Message} {L : QueryLog SigningSpec} {sig : Signature} :
    ¬Unsigned (L ++ [⟨m, some sig⟩]) (m, sig.randomness) := fun h =>
  h ⟨m, some sig⟩ (List.mem_append_right _ (List.mem_singleton_self _)) sig rfl ⟨rfl, rfl⟩

section SignGood

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem interpThen_some {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

theorem interpThen_none {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

end SignGood

end FORS.Security.ForsPotential
